/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.AlgebraicTopology.SingularSet
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Data.Fin.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
/-!
# A continuous-group Borel model from literal orbit quotients

Let a topological group `G` act continuously on a space `Z`. Degree `n` of
the bar construction is the quotient of `G^(n+1) × Z` by the diagonal
action, with its quotient topology; coordinate reindexing makes these levels
a simplicial space. Applying the singular-set functor levelwise, taking the
diagonal, and geometrically realizing it gives a concrete model of the
homotopy quotient `EG ×_G Z`. The constructions forming this model require
the group to be topological and the action to be continuous
(`[IsTopologicalGroup G] [ContinuousSMul G Z]`), so that they always have
their homotopy-quotient interpretation; the levels themselves only use the
orbit relation.

An invariant continuous map constructs the canonical augmentation to the
quotient. Equivariant maps give actual realization maps. The degree-zero
orbit space is normalized by the proved homeomorphism `[g, x] ↦ g⁻¹x`.
No freely named classifying space or equivariant cohomology carrier is used.

Reference: Segal, *Classifying spaces and spectral sequences*, Publ. Math.
IHES 34 (1968), §§2--3. Existing Mathlib singular-set and geometric-realization
functors are reused. TauCeti's classifying-space countable join is a discrete-
group construction; it is not identified with this continuous-group model.
-/

@[expose] public noncomputable section
open _root_.CategoryTheory _root_.Opposite
open scoped Simplicial
namespace MathlibExt.Topology.ContinuousBorel
variable (G : Type) [Group G] [TopologicalSpace G]
variable (Z : TopCat.{0}) [MulAction G Z]

/-- The homogeneous coordinates of bar degree `n`: `G^(n+1) × Z`, with the
diagonal action of `G`. -/
abbrev Homogeneous (n : ℕ) := (Fin (n + 1) → G) × Z

/-- Bar degree `n`: the orbit space of the diagonal action on `G^(n+1) × Z`,
with the quotient topology. -/
abbrev BarLevel (n : ℕ) := Quotient (MulAction.orbitRel G (Homogeneous G Z n))

/-- Reindexing of homogeneous coordinates along a map of vertices. -/
def reindex {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    Homogeneous G Z n → Homogeneous G Z m := fun p => (p.1 ∘ f, p.2)

omit [TopologicalSpace G] in
/-- Reindexing commutes with the diagonal action. -/
theorem reindex_equivariant {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1))
    (g : G) (p : Homogeneous G Z n) :
    reindex G Z f (g • p) = g • reindex G Z f p := rfl

/-- The induced map of bar levels. -/
def barMap {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    BarLevel G Z n → BarLevel G Z m :=
  Quotient.map (reindex G Z f) (by
    intro a b h
    change a ∈ MulAction.orbit G b at h
    change reindex G Z f a ∈ MulAction.orbit G (reindex G Z f b)
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp h
    exact MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩)

omit [Group G] [MulAction G Z] in
/-- Reindexing is continuous. -/
theorem reindex_continuous {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    Continuous (reindex G Z f) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro i
    exact (continuous_apply (f i)).comp continuous_fst
  · exact continuous_snd

/-- The induced map of bar levels is continuous. -/
theorem barMap_continuous {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    Continuous (barMap G Z f) := by
  exact continuous_coinduced_dom.2
    (continuous_quot_mk.comp (reindex_continuous G Z f))

/-- The bar construction of a continuous action, as a simplicial space. -/
def bar [IsTopologicalGroup G] [ContinuousSMul G Z] : SimplicialObject TopCat.{0} where
  obj n := TopCat.of (BarLevel G Z n.unop.len)
  map f := TopCat.ofHom ⟨barMap G Z f.unop.toOrderHom, barMap_continuous G Z _⟩
  map_id n := by ext p; induction p using Quotient.inductionOn; rfl
  map_comp f g := by ext p; induction p using Quotient.inductionOn; rfl

/-- The diagonal of the levelwise singular sets of the bar construction. -/
abbrev diagonalSingular [IsTopologicalGroup G] [ContinuousSMul G Z] : SSet.{0} :=
  Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj (bar G Z ⋙ TopCat.toSSet)

/-- The Borel model of the homotopy quotient: the geometric realization of
`diagonalSingular`. -/
abbrev borel [IsTopologicalGroup G] [ContinuousSMul G Z] : TopCat.{0} :=
  SSet.toTop.obj (diagonalSingular G Z)

/-- The diagonal of a simplicial object in simplicial sets. -/
abbrev diagonalFunctor : (SimplexCategoryᵒᵖ ⥤ SSet.{0}) ⥤ SSet.{0} :=
  Functor.uncurry ⋙ (Functor.whiskeringLeft _ _ _).obj (Functor.diag SimplexCategoryᵒᵖ)

/-- The diagonal of a constant simplicial object is the object itself. -/
def diagonalConstIso (A : SSet.{0}) :
    diagonalFunctor.obj ((Functor.const SimplexCategoryᵒᵖ).obj A) ≅ A :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp [diagonalFunctor])

variable {G Z} {Q : TopCat.{0}}

/-- On bar level `n`, an invariant map induces the map `[g, x] ↦ q x`. -/
def quotientAugmentation (q : Z ⟶ Q) (hq : ∀ (g : G) (x : Z), q (g • x) = q x)
    (n : ℕ) : BarLevel G Z n → Q :=
  Quotient.lift (fun p => q p.2) (by
    intro a b h
    change a ∈ MulAction.orbit G b at h
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp h
    exact hq g b.2)

/-- The augmentation of the bar construction to the constant simplicial space
on the quotient, induced by an invariant map. -/
def barAugmentation [IsTopologicalGroup G] [ContinuousSMul G Z] (q : Z ⟶ Q)
    (hq : ∀ (g : G) (x : Z), q (g • x) = q x) :
    bar G Z ⟶ (Functor.const SimplexCategoryᵒᵖ).obj Q where
  app n := TopCat.ofHom ⟨quotientAugmentation q hq n.unop.len,
    continuous_coinduced_dom.2 (q.hom.continuous.comp continuous_snd)⟩
  naturality i j f := by ext p; induction p using Quotient.inductionOn; rfl

/-- The augmentation on the diagonal singular simplicial set. -/
def diagonalAugmentation [IsTopologicalGroup G] [ContinuousSMul G Z] (q : Z ⟶ Q)
    (hq : ∀ (g : G) (x : Z), q (g • x) = q x) :
    diagonalSingular G Z ⟶ TopCat.toSSet.obj Q :=
  diagonalFunctor.map (Functor.whiskerRight (barAugmentation q hq) TopCat.toSSet) ≫
    diagonalFunctor.map (Functor.constComp SimplexCategoryᵒᵖ Q TopCat.toSSet).hom ≫
      (diagonalConstIso (TopCat.toSSet.obj Q)).hom

/-- The canonical map from the Borel model to the quotient: the realization
of the augmentation followed by the counit of the singular-set adjunction. -/
def borelToQuotient [IsTopologicalGroup G] [ContinuousSMul G Z] (q : Z ⟶ Q)
    (hq : ∀ (g : G) (x : Z), q (g • x) = q x) :
    borel G Z ⟶ Q :=
  SSet.toTop.map (diagonalAugmentation q hq) ≫ sSetTopAdj.counit.app Q

variable {W : TopCat.{0}} [MulAction G W]

/-- On bar level `n`, an equivariant map induces `[g, x] ↦ [g, f x]`. -/
def levelEquivariantMap (f : Z ⟶ W) (hf : ∀ (g : G) (x : Z), f (g • x) = g • f x)
    (n : ℕ) : BarLevel G Z n → BarLevel G W n :=
  Quotient.map (fun p => (p.1, f p.2)) (by
    intro a b h
    change a ∈ MulAction.orbit G b at h
    change _ ∈ MulAction.orbit G _
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp h
    apply MulAction.mem_orbit_iff.mpr
    exact ⟨g, Prod.ext rfl (hf g b.2).symm⟩)

/-- The map of bar constructions induced by an equivariant map. -/
def barEquivariantMap [IsTopologicalGroup G] [ContinuousSMul G Z] [ContinuousSMul G W]
    (f : Z ⟶ W) (hf : ∀ (g : G) (x : Z), f (g • x) = g • f x) :
    bar G Z ⟶ bar G W where
  app n := TopCat.ofHom ⟨levelEquivariantMap f hf n.unop.len,
    continuous_coinduced_dom.2
      (continuous_quot_mk.comp (continuous_fst.prodMk (f.hom.continuous.comp continuous_snd)))⟩
  naturality i j a := by ext p; induction p using Quotient.inductionOn; rfl

/-- The map of Borel models induced by an equivariant map. -/
def borelMap [IsTopologicalGroup G] [ContinuousSMul G Z] [ContinuousSMul G W]
    (f : Z ⟶ W) (hf : ∀ (g : G) (x : Z), f (g • x) = g • f x) :
    borel G Z ⟶ borel G W :=
  SSet.toTop.map
    (diagonalFunctor.map (Functor.whiskerRight (barEquivariantMap f hf) TopCat.toSSet))

variable (G Z)

/-- Bar level zero is homeomorphic to `Z`, by `[g, x] ↦ g⁻¹ • x`. -/
def levelZero [IsTopologicalGroup G] [ContinuousSMul G Z] : BarLevel G Z 0 ≃ₜ Z where
  toFun := Quotient.lift (fun p : Homogeneous G Z 0 => (p.1 0)⁻¹ • p.2) (by
    intro a b h
    change a ∈ MulAction.orbit G b at h
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp h
    change (g * b.1 0)⁻¹ • (g • b.2) = (b.1 0)⁻¹ • b.2
    rw [mul_inv_rev, mul_smul, inv_smul_smul])
  invFun x := Quotient.mk'' ((fun _ : Fin 1 => 1), x)
  left_inv p := by
    induction p using Quotient.inductionOn with | _ p =>
      apply Quotient.sound
      change _ ∈ MulAction.orbit G p
      apply MulAction.mem_orbit_iff.mpr
      refine ⟨(p.1 0)⁻¹, Prod.ext ?_ rfl⟩
      funext i
      have hi : i = 0 := Fin.eq_zero i
      simp [hi]
  right_inv x := by simp
  continuous_toFun := continuous_coinduced_dom.2
    (((continuous_apply (0 : Fin 1)).comp continuous_fst).inv.smul continuous_snd)
  continuous_invFun := continuous_quot_mk.comp (continuous_const.prodMk continuous_id)

end MathlibExt.Topology.ContinuousBorel
