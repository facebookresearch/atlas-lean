/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Actual truncated discs, jet functors and formal arc limits

The disc is Spec k[t]/(t)^(n+1). Jets on every scheme-valued test are
morphisms from its actual product with that disc. Truncation is induced
by the literal quotient ring map. The arc functor is the inverse limit
of these exact functors, not an arbitrarily named set of arcs.

Representation is a separate construction request. For an affine target `Spec B`,
the source identifies arcs with ring maps `B → A⟦t⟧`, that is, with morphisms out of
`Spec A⟦t⟧`; for general targets its field-valued assertion is kept distinct.

Reference: Ein--Mustata, *Jet schemes and singularities*,
arXiv:math/0612862, equation (2.1), Proposition 2.2 and section 3.
Generic polynomial quotients, fibre products, Yoneda and limits are
completed Mathlib primitives. The adapters below are original definitions.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.JetArcFunctors

open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry

universe u

variable (k : Type u) [CommRing k]

abbrev OverBase := Over (Spec (.of k))

/-- Finite type is the conjunction of the two native morphism properties. -/
def IsFiniteTypeOverBase (X : OverBase k) : Prop :=
  LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom

/-- The actual zero-section ideal in the affine line. -/
def augmentationIdeal : Ideal (Polynomial k) := Ideal.span {Polynomial.X}

/-- No reduction of the nilpotent truncated parameter. -/
abbrev TruncatedRing (n : ℕ) := Polynomial k ⧸ augmentationIdeal k ^ (n + 1)

def disc (n : ℕ) : OverBase k := Over.mk (Spec.algebraMap k (TruncatedRing k n))

/-- The actual quotient map defining truncation. -/
def truncationRing {m n : ℕ} (h : m ≤ n) :
    TruncatedRing k n →ₐ[k] TruncatedRing k m :=
  Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (Nat.succ_le_succ h))

def discInclusion {m n : ℕ} (h : m ≤ n) : disc k m ⟶ disc k n :=
  Over.homMk (Spec.map (CommRingCat.ofHom (truncationRing k h).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hc : (truncationRing k h).toRingHom.comp
        (algebraMap k (TruncatedRing k n)) = algebraMap k (TruncatedRing k m) :=
      RingHom.ext fun a ↦ (truncationRing k h).commutes a
    rw [hc])

@[simp] theorem discInclusion_refl (n : ℕ) : discInclusion k (le_refl n) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  simp [discInclusion, truncationRing]
  rfl

@[simp] theorem discInclusion_comp {l m n : ℕ} (h : l ≤ m) (j : m ≤ n) :
    discInclusion k h ≫ discInclusion k j = discInclusion k (h.trans j) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hc : (truncationRing k h).toRingHom.comp (truncationRing k j).toRingHom =
      (truncationRing k (h.trans j)).toRingHom := by
    apply RingHom.ext
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rfl
  rw [hc]

/-- Actual product with the nilpotent disc over the coefficient base. -/
abbrev thickening (n : ℕ) : OverBase k ⥤ OverBase k := prod.functor.obj (disc k n)

/-- The disc diagram consists of the literal quotient-induced inclusions. -/
def discTower : ℕ ⥤ OverBase k where
  obj n := disc k n
  map f := discInclusion k (leOfHom f)
  map_id n := discInclusion_refl k n
  map_comp f g := (discInclusion_comp k (leOfHom f) (leOfHom g)).symm

/-- Product, opposite and Yoneda precomposition are native functors, so
the diagram coherence is inherited from those completed operations. -/
def jetTower (X : OverBase k) : ℕᵒᵖ ⥤ ((OverBase k)ᵒᵖ ⥤ Type u) :=
  (discTower k ⋙ prod.functor).op ⋙ Functor.opHom (OverBase k) (OverBase k) ⋙
    (Functor.whiskeringRight (OverBase k)ᵒᵖ (OverBase k)ᵒᵖ (Type u)).obj (yoneda.obj X)

/-- The genuine jet functor on all scheme-valued tests. -/
abbrev jetFunctor (n : ℕ) (X : OverBase k) : (OverBase k)ᵒᵖ ⥤ Type u :=
  (jetTower k X).obj (op n)

/-- Restriction along the actual closed disc inclusion. -/
def truncate {m n : ℕ} (h : m ≤ n) (X : OverBase k) :
    jetFunctor k n X ⟶ jetFunctor k m X :=
  (jetTower k X).map (homOfLE h).op

@[simp] theorem truncate_refl (n : ℕ) (X : OverBase k) :
    truncate k (le_refl n) X = 𝟙 _ := by
  exact (jetTower k X).map_id (op n)

/-- Postcomposition is the actual functorial map on jets. -/
def jetMap (n : ℕ) {X Y : OverBase k} (f : X ⟶ Y) :
    jetFunctor k n X ⟶ jetFunctor k n Y :=
  Functor.whiskerLeft (thickening k n).op (yoneda.map f)

/-- Formal arc values are the literal limit of compatible truncations. -/
def arcFunctor (X : OverBase k) : (OverBase k)ᵒᵖ ⥤ Type u := limit (jetTower k X)

def arcProjection (X : OverBase k) (n : ℕ) : arcFunctor k X ⟶ jetFunctor k n X :=
  limit.π (jetTower k X) (op n)

/-- A representing jet scheme is characterized by its natural test maps. -/
structure JetModel (n : ℕ) (X : OverBase k) where
  scheme : OverBase k
  representation : yoneda.obj scheme ≅ jetFunctor k n X

/-- An arc scheme is characterized by the actual compatible jet limit. -/
structure ArcModel (X : OverBase k) where
  scheme : OverBase k
  representation : yoneda.obj scheme ≅ arcFunctor k X

/-- The represented truncation is fixed by the actual quotient operation. -/
def representedTruncation {m n : ℕ} {X : OverBase k} (h : m ≤ n)
    (N : JetModel k n X) (M : JetModel k m X) : N.scheme ⟶ M.scheme :=
  Yoneda.fullyFaithful.preimage
    (N.representation.hom ≫ truncate k h X ≫ M.representation.inv)

/-- The nilpotent parameter in the genuine test ring. -/
def parameter (A : Type u) [CommRing A] (n : ℕ) : TruncatedRing A n :=
  Ideal.Quotient.mk _ Polynomial.X

/-- Literal order-at-least-r contact on an affine jet, retaining nilpotents. -/
def affineContact (B A : Type u) [CommRing B] [CommRing A]
    [Algebra k B] [Algebra k A] (n r : ℕ) (I : Ideal B)
    (f : B →ₐ[k] TruncatedRing A n) : Prop :=
  ∀ b ∈ I, f b ∈ (Ideal.span {parameter A n}) ^ r

end MathlibExt.AlgebraicGeometry.JetArcFunctors
