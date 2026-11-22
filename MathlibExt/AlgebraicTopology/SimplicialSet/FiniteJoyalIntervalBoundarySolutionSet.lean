/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalBoundedWeakSubobjects
public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalCountableArrows
public import MathlibExt.AlgebraicTopology.ModelCategory.AccessibleMorphismProperty

/-!
# The boundary solution set for finite-interval testing equivalences

The family indexes every boundary-to-representative square. Boundary
factorization and countable enlargement factor every original square into
an arbitrary weak arrow through this family, with both components retained.
This is the explicit Smith solution-set specialization of Cisinski,
Lemmas 2.4.38 and 2.4.39 (2026); no model or accessibility premise is used.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace SSet.joyalInterval

/-- Interpolate a whole boundary square through the actual countable
pullback projection furnished by bounded enlargement. -/
private theorem exists_countable_boundary_interpolation (n : ℕ)
    (f : Arrow SSet.{u})
    (hf : productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions f.hom)
    (sq : Arrow.mk (boundary.{u} n).ι ⟶ f) :
    ∃ (P V : SSet.{u}) (k : P ⟶ V), Countable P.N ∧ Countable V.N ∧
      productPrecylinder.testingTrivialCofibrations auxiliaryAnodyneExtensions k ∧
      ∃ (δ : Arrow.mk (boundary.{u} n).ι ⟶ Arrow.mk k)
        (β : Arrow.mk k ⟶ f), δ ≫ β = sq := by
  let W := productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions
  let d := modelCategoryQuillen.monoFactorizationData f.hom
  have : Mono d.i := d.hi
  have hp : W d.p :=
    productPrecylinder.rlp_monomorphisms_le_testingEquivalences
      auxiliaryAnodyneExtensions d.p d.hp
  have hj : W d.i := W.of_postcomp d.i d.p hp (by rwa [d.fac])
  have : HasLiftingProperty (boundary.{u} n).ι d.p := d.hp _ (by infer_instance)
  let liftSq : CommSq (sq.left ≫ d.i) (boundary.{u} n).ι d.p sq.right :=
    ⟨by rw [Category.assoc, d.fac]; exact sq.w⟩
  let ℓ := liftSq.lift
  let U := Subcomplex.range ℓ
  have hU : Countable U.toSSet.N := by
    dsimp [U]
    infer_instance
  obtain ⟨V, hUV, hVN, _, hPN, _, hk⟩ :=
    exists_countable_testing_enlargement d.i hj U hU
  let k := pullback.snd d.i V.ι
  let ℓV := Subcomplex.lift ℓ hUV
  have hℓV : ℓV ≫ V.ι = ℓ := Subcomplex.lift_ι ℓ hUV
  have comm : sq.left ≫ d.i = ((boundary.{u} n).ι ≫ ℓV) ≫ V.ι := by
    rw [Category.assoc, hℓV]
    exact liftSq.fac_left.symm
  let aV := pullback.lift sq.left ((boundary.{u} n).ι ≫ ℓV) comm
  let δ : Arrow.mk (boundary.{u} n).ι ⟶ Arrow.mk k :=
    Arrow.homMk aV ℓV (pullback.lift_snd ..)
  let β : Arrow.mk k ⟶ f :=
    Arrow.homMk (pullback.fst d.i V.ι) (V.ι ≫ d.p) (by
      calc
        pullback.fst d.i V.ι ≫ f.hom =
            pullback.fst d.i V.ι ≫ (d.i ≫ d.p) :=
          congrArg (fun e => pullback.fst d.i V.ι ≫ e) d.fac.symm
        _ = (pullback.fst d.i V.ι ≫ d.i) ≫ d.p := (Category.assoc ..).symm
        _ = (pullback.snd d.i V.ι ≫ V.ι) ≫ d.p :=
          congrArg (fun e => e ≫ d.p) (pullback.condition (f := d.i) (g := V.ι))
        _ = k ≫ (V.ι ≫ d.p) := Category.assoc ..)
  have hfac : δ ≫ β = sq := by
    apply Arrow.hom_ext
    · change aV ≫ pullback.fst d.i V.ι = sq.left
      exact pullback.lift_fst ..
    · change ℓV ≫ (V.ι ≫ d.p) = sq.right
      rw [← Category.assoc, hℓV]
      exact liftSq.fac_right
  exact ⟨pullback d.i V.ι, V.toSSet, k, hPN, hVN, hk, δ, β, hfac⟩

/-- Every literal boundary has a size-u weakly initial family in its
comma category with the full category of testing-equivalence arrows. -/
theorem testingEquivalences_boundary_solution_set
    {A B : SSet.{u}} (i : A ⟶ B) (hi : modelCategoryQuillen.I i) :
    ∃ (S : Type u)
      (q : S → (productPrecylinder.testingEquivalences
        auxiliaryAnodyneExtensions).arrowObjectProperty.FullSubcategory)
      (h : ∀ s, Arrow.mk i ⟶
        (productPrecylinder.testingEquivalences
          auxiliaryAnodyneExtensions).arrowObjectProperty.ι.obj (q s)),
      ∀ (T : (productPrecylinder.testingEquivalences
          auxiliaryAnodyneExtensions).arrowObjectProperty.FullSubcategory)
        (sq : Arrow.mk i ⟶
          (productPrecylinder.testingEquivalences
            auxiliaryAnodyneExtensions).arrowObjectProperty.ι.obj T),
        ∃ (s : S) (ψ : q s ⟶ T),
          h s ≫ (productPrecylinder.testingEquivalences
            auxiliaryAnodyneExtensions).arrowObjectProperty.ι.map ψ = sq := by
  classical
  let W := productPrecylinder.testingEquivalences auxiliaryAnodyneExtensions
  obtain ⟨Γ, A₀, B₀, g, _, hg, hrep⟩ := exists_countable_testing_representatives.{u}
  let S : Type u := Σ γ : Γ, (Arrow.mk i ⟶ Arrow.mk (g γ))
  let q : S → W.arrowObjectProperty.FullSubcategory :=
    fun s => ⟨Arrow.mk (g s.1), (hg s.1).1.2⟩
  let h (s : S) : Arrow.mk i ⟶ W.arrowObjectProperty.ι.obj (q s) := s.2
  refine ⟨S, q, h, ?_⟩
  intro T sq
  change MorphismProperty.ofHoms (fun n : ℕ => (boundary.{u} n).ι) i at hi
  obtain ⟨n, hI⟩ := (MorphismProperty.ofHoms_iff _ i).mp hi
  let eI : Arrow.mk i ≅ Arrow.mk (boundary.{u} n).ι := eqToIso hI
  obtain ⟨P, V, k, hP, hV, hk, δ, β, hfac⟩ :=
    exists_countable_boundary_interpolation n T.obj T.property (eI.inv ≫ sq)
  obtain ⟨γ, eX, eY, square⟩ := hrep P V k hP hV hk
  let E : Arrow.mk (g γ) ≅ Arrow.mk k := Arrow.isoMk' (g γ) k eX eY square
  let s : S := ⟨γ, (eI.hom ≫ δ) ≫ E.inv⟩
  let ψ : q s ⟶ T := ObjectProperty.homMk (E.hom ≫ β)
  refine ⟨s, ψ, ?_⟩
  change ((eI.hom ≫ δ) ≫ E.inv) ≫ (E.hom ≫ β) = sq
  calc
    _ = eI.hom ≫ (δ ≫ β) := by simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = eI.hom ≫ (eI.inv ≫ sq) := by rw [hfac]
    _ = sq := by simp only [Iso.hom_inv_id_assoc]

end SSet.joyalInterval
