/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.FiniteLocallyFreeQuotient
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

-- `exactSource` consumer with the original binders.
example {X R : Scheme.{u}} (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hmono : ∀ {T : Scheme.{u}} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b)
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    (haff : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ r : R, s r = x → t r ∈ U) :
    ∃ (Y : Scheme.{u}) (p : X ⟶ Y) (w : s ≫ p = t ≫ p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback s t p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) :=
  Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation s t hmono hequiv haff

-- Higher-universe consumer.
example {X R : Scheme.{u + 1}} (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hmono : ∀ {T : Scheme.{u + 1}} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b)
    (hequiv : ∀ T : Scheme.{u + 1},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    (haff : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ r : R, s r = x → t r ∈ U) :
    ∃ (Y : Scheme.{u + 1}) (p : X ⟶ Y), s ≫ p = t ≫ p ∧ Surjective p := by
  obtain ⟨Y, p, w, -, -, -, h, -⟩ :=
    Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation s t hmono hequiv haff
  exact ⟨Y, p, w, h⟩

/-- Points `x y : T ⟶ X` are related by the kernel pair of `p` exactly when `x ≫ p = y ≫ p`. -/
private theorem kernelPair_rel_iff {X Y T : Scheme.{u}} (p : X ⟶ Y) (x y : T ⟶ X) :
    (∃ φ : T ⟶ pullback p p, φ ≫ pullback.fst p p = x ∧ φ ≫ pullback.snd p p = y) ↔
      x ≫ p = y ≫ p :=
  ⟨fun ⟨φ, h₁, h₂⟩ => by rw [← h₁, ← h₂, Category.assoc, Category.assoc, pullback.condition],
    fun h => ⟨pullback.lift x y h, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩⟩

-- Concrete use: the kernel pair of a finite locally free surjection `p` out of an affine scheme
-- meets every hypothesis, and the quotient the theorem returns is the target of `p`.
example {X Y : Scheme.{u}} [IsAffine X] (p : X ⟶ Y) [IsFinite p] [Flat p]
    [LocallyOfFinitePresentation p] [Surjective p] :
    ∃ (Q : Scheme.{u}) (q : X ⟶ Q) (e : Q ≅ Y), q ≫ e.hom = p := by
  obtain ⟨Q, q, w, -, -, -, -, -, ⟨hq⟩⟩ :=
    Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation
      (pullback.fst p p) (pullback.snd p p) (fun _ _ h₁ h₂ => pullback.hom_ext h₁ h₂)
      (fun T => ⟨fun x => (kernelPair_rel_iff p x x).2 rfl,
        fun h => (kernelPair_rel_iff p _ _).2 ((kernelPair_rel_iff p _ _).1 h).symm,
        fun h h' => (kernelPair_rel_iff p _ _).2
          (((kernelPair_rel_iff p _ _).1 h).trans ((kernelPair_rel_iff p _ _).1 h'))⟩)
      (fun _ => ⟨⊤, isAffineOpen_top X, fun _ _ => trivial⟩)
  have hk : IsKernelPair p (pullback.fst p p) (pullback.snd p p) := IsPullback.of_hasPullback p p
  have hp : IsColimit (Cofork.ofπ p hk.w) := hk.toCoequalizer (regularEpiOfEffectiveEpi p)
  exact ⟨Q, q, hq.coconePointUniqueUpToIso hp,
    hq.comp_coconePointUniqueUpToIso_hom hp WalkingParallelPair.one⟩
