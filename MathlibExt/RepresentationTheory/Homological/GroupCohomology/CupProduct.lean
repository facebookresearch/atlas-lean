/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.RepresentationTheory.Homological.Resolution
public import MathlibExt.Algebra.Homology.GradedPairingHomology
public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney.LinearYonedaPairing
public import MathlibExt.CategoryTheory.Monoidal.PreservesColimits

/-!
# Arbitrary-degree group-cohomology cup products

The diagonal on the simplicial universal cover `EG` linearizes
oplax-monoidally.  Composing it with the Alexander--Whitney chain map gives a
diagonal on the standard resolution, hence on the isomorphic bar
resolution.  The general linear-Yoneda cochain pairing then yields a
Koszul-compatible arbitrary-degree pairing on inhomogeneous group cochains
and a cup morphism on group cohomology.

The existing explicit degree-`(1,1)` and degree-`(1,2)` cup APIs remain
separate low-degree interfaces. Compatibility with the general construction
requires an additional comparison theorem.

## Main declarations

* `groupCohomology.universalCoverDiagonal`
* `groupCohomology.linearizedUniversalCoverDiagonal`
* `groupCohomology.standardComplexDiagonal`
* `groupCohomology.barComplexDiagonal`
* `groupCohomology.barCochainCupPairing`
* `groupCohomology.inhomogeneousCupPairing`
* `groupCohomology.inhomogeneousCupPairing_apply`
* `groupCohomology.cup`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace groupCohomology

variable (G : Type u) [Group G]

/-- The simplicial diagonal of the universal cover of the group
classifying space. -/
def universalCoverDiagonal :
    classifyingSpaceUniversalCover G ⟶
      classifyingSpaceUniversalCover G ⊗ classifyingSpaceUniversalCover G where
  app n :=
    { hom := ↾(fun x => (x, x))
      comm := fun _ => rfl }
  naturality := by
    intro X Y f
    ext x
    rfl

variable (k : Type u) [CommRing k]

/-- Postcomposition by the linearization functor on simplicial objects. -/
noncomputable abbrev linearizationOnSimplicialObjects :
    SimplicialObject (Action (Type u) G) ⥤
      SimplicialObject (Rep k G) :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ _ _).obj
    (Rep.linearization k G)

/-- The universal-cover diagonal after oplax-monoidal linearization. -/
noncomputable def linearizedUniversalCoverDiagonal :
    classifyingSpaceUniversalCover G ⋙ Rep.linearization k G ⟶
      (classifyingSpaceUniversalCover G ⋙ Rep.linearization k G) ⊗
        (classifyingSpaceUniversalCover G ⋙ Rep.linearization k G) :=
  (linearizationOnSimplicialObjects G k).map (universalCoverDiagonal G) ≫
    Functor.OplaxMonoidal.δ (linearizationOnSimplicialObjects G k)
      (classifyingSpaceUniversalCover G) (classifyingSpaceUniversalCover G)

section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The linearized universal-cover diagonal sends a basis simplex
to the pure tensor of two copies of that simplex. -/
@[simp]
theorem linearizedUniversalCoverDiagonal_app_apply_single
    (n : ℕ) (u : Fin (n + 1) → G) :
    ((linearizedUniversalCoverDiagonal G k).app
        (Opposite.op (SimplexCategory.mk n))).hom
        (MonoidAlgebra.single u 1) =
      MonoidAlgebra.single u 1 ⊗ₜ[k] MonoidAlgebra.single u 1 := by
  have hmap := Representation.linearizeMap_single (k := k)
    ((universalCoverDiagonal G).app
      (Opposite.op (SimplexCategory.mk n))) u 1
  change (Representation.LinearizeMonoidal.δ
      ((classifyingSpaceUniversalCover G).obj
        (Opposite.op (SimplexCategory.mk n)))
      ((classifyingSpaceUniversalCover G).obj
        (Opposite.op (SimplexCategory.mk n))))
      ((Representation.linearizeMap ((universalCoverDiagonal G).app
        (Opposite.op (SimplexCategory.mk n))))
        (MonoidAlgebra.single u 1)) = _
  erw [hmap]
  erw [Representation.LinearizeMonoidal.δ_apply_single]
  rfl

/-- Degreewise form of
`linearizedUniversalCoverDiagonal_app_apply_single` on the alternating-face
complex. -/
@[simp]
theorem alternatingFaceMapComplex_linearizedUniversalCoverDiagonal_f_apply_single
    (n : ℕ) (u : Fin (n + 1) → G) :
    (((AlgebraicTopology.alternatingFaceMapComplex (Rep k G)).map
        (linearizedUniversalCoverDiagonal G k)).f n).hom
        (MonoidAlgebra.single u 1) =
      MonoidAlgebra.single u 1 ⊗ₜ[k] MonoidAlgebra.single u 1 := by
  change ((linearizedUniversalCoverDiagonal G k).app
      (Opposite.op (SimplexCategory.mk n))).hom
      (MonoidAlgebra.single u 1) = _
  exact linearizedUniversalCoverDiagonal_app_apply_single G k n u

/-- A front-face map on the linearized universal cover restricts a basis
simplex along the front subinterval inclusion. -/
@[simp]
theorem linearizedUniversalCover_frontFace_apply_single
    {p q n : ℕ} (h : p + q = n) (u : Fin (n + 1) → G) (r : k) :
    (AlgebraicTopology.AlexanderWhitney.frontFace
        (classifyingSpaceUniversalCover G ⋙ Rep.linearization k G) h).hom
        (MonoidAlgebra.single u r) =
      MonoidAlgebra.single
        (fun i => u ((AlgebraicTopology.AlexanderWhitney.frontInclusion
          p q n h).toOrderHom i)) r := by
  change Representation.linearizeMap
      ((classifyingSpaceUniversalCover G).map
        (AlgebraicTopology.AlexanderWhitney.frontInclusion p q n h).op)
      (MonoidAlgebra.single u r) = _
  rw [Representation.linearizeMap_single]
  rfl

/-- A back-face map on the linearized universal cover restricts a basis
simplex along the back subinterval inclusion. -/
@[simp]
theorem linearizedUniversalCover_backFace_apply_single
    {p q n : ℕ} (h : p + q = n) (u : Fin (n + 1) → G) (r : k) :
    (AlgebraicTopology.AlexanderWhitney.backFace
        (classifyingSpaceUniversalCover G ⋙ Rep.linearization k G) h).hom
        (MonoidAlgebra.single u r) =
      MonoidAlgebra.single
        (fun i => u ((AlgebraicTopology.AlexanderWhitney.backInclusion
          p q n h).toOrderHom i)) r := by
  change Representation.linearizeMap
      ((classifyingSpaceUniversalCover G).map
        (AlgebraicTopology.AlexanderWhitney.backInclusion p q n h).op)
      (MonoidAlgebra.single u r) = _
  rw [Representation.linearizeMap_single]
  rfl

end

/-- The Alexander--Whitney diagonal on the standard group resolution. -/
noncomputable def standardComplexDiagonal :
    Rep.standardComplex k G ⟶
      HomologicalComplex.tensorObj
        (Rep.standardComplex k G) (Rep.standardComplex k G) :=
  (AlgebraicTopology.alternatingFaceMapComplex (Rep k G)).map
      (linearizedUniversalCoverDiagonal G k) ≫
    AlgebraicTopology.AlexanderWhitney.alternatingMap
      (classifyingSpaceUniversalCover G ⋙ Rep.linearization k G)
      (classifyingSpaceUniversalCover G ⋙ Rep.linearization k G)

/-- The Alexander--Whitney diagonal transported from the standard
resolution to the bar resolution. -/
noncomputable def barComplexDiagonal :
    Rep.barComplex k G ⟶
      HomologicalComplex.tensorObj (Rep.barComplex k G) (Rep.barComplex k G) :=
  (Rep.barComplex.isoStandardComplex k G).hom ≫
    standardComplexDiagonal G k ≫
    HomologicalComplex.tensorHom
      (Rep.barComplex.isoStandardComplex k G).inv
      (Rep.barComplex.isoStandardComplex k G).inv

set_option backward.isDefEq.respectTransparency false in
/-- After projection to a chosen bidegree, the bar diagonal is the
corresponding front/back Alexander--Whitney split, with the two cochains
transported from the bar resolution to the standard resolution. -/
theorem barComplexDiagonal_comp_linearYonedaPairingDescOfEq
    {M N P : Rep k G} (mu : M ⊗ N ⟶ P)
    (n : ℕ) (s : Fin (n + 1))
    (phi : (Rep.barComplex k G).X s ⟶ M)
    (psi : (Rep.barComplex k G).X (n - s) ⟶ N) :
    (barComplexDiagonal G k).f n ≫
        HomologicalComplex.linearYonedaPairingDescOfEq (Rep k G) mu
          s (n - s) n (by omega) phi psi =
      (Rep.barComplex.isoStandardComplex k G).hom.f n ≫
        ((AlgebraicTopology.alternatingFaceMapComplex (Rep k G)).map
          (linearizedUniversalCoverDiagonal G k)).f n ≫
        (AlgebraicTopology.AlexanderWhitney.frontFace
            (classifyingSpaceUniversalCover G ⋙ Rep.linearization k G)
            (show s + (n - s) = n by omega) ⊗ₘ
          AlgebraicTopology.AlexanderWhitney.backFace
            (classifyingSpaceUniversalCover G ⋙ Rep.linearization k G)
            (show s + (n - s) = n by omega)) ≫
        (((Rep.barComplex.isoStandardComplex k G).inv.f s ≫ phi) ⊗ₘ
          ((Rep.barComplex.isoStandardComplex k G).inv.f (n - s) ≫ psi)) ≫
        mu := by
  rw [barComplexDiagonal]
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [HomologicalComplex.linearYonedaPairingDescOfEq_naturality]
  rw [standardComplexDiagonal]
  simp only [HomologicalComplex.comp_f,
    AlgebraicTopology.AlexanderWhitney.alternatingMap_f, Category.assoc]
  rw [AlgebraicTopology.AlexanderWhitney.alternatingComponent_comp_linearYonedaPairingDescOfEq]

set_option backward.isDefEq.respectTransparency false in
/-- At total degree `p + q`, the bar diagonal followed by a linear-Yoneda
pairing descriptor is the corresponding front/back Alexander--Whitney split. -/
theorem barComplexDiagonal_comp_linearYonedaPairingDesc
    {M N P : Rep k G} (mu : M ⊗ N ⟶ P)
    (p q : ℕ)
    (phi : (Rep.barComplex k G).X p ⟶ M)
    (psi : (Rep.barComplex k G).X q ⟶ N) :
    (barComplexDiagonal G k).f (p + q) ≫
        HomologicalComplex.linearYonedaPairingDesc (Rep k G) mu
          p q phi psi =
      (Rep.barComplex.isoStandardComplex k G).hom.f (p + q) ≫
        ((AlgebraicTopology.alternatingFaceMapComplex (Rep k G)).map
          (linearizedUniversalCoverDiagonal G k)).f (p + q) ≫
        (AlgebraicTopology.AlexanderWhitney.frontFace
            (classifyingSpaceUniversalCover G ⋙ Rep.linearization k G)
            (show p + q = p + q by rfl) ⊗ₘ
          AlgebraicTopology.AlexanderWhitney.backFace
            (classifyingSpaceUniversalCover G ⋙ Rep.linearization k G)
            (show p + q = p + q by rfl)) ≫
        (((Rep.barComplex.isoStandardComplex k G).inv.f p ≫ phi) ⊗ₘ
          ((Rep.barComplex.isoStandardComplex k G).inv.f q ≫ psi)) ≫
        mu := by
  rw [barComplexDiagonal]
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [HomologicalComplex.linearYonedaPairingDesc_naturality]
  rw [standardComplexDiagonal]
  simp only [HomologicalComplex.comp_f,
    AlgebraicTopology.AlexanderWhitney.alternatingMap_f, Category.assoc]
  rw [AlgebraicTopology.AlexanderWhitney.alternatingComponent_comp_linearYonedaPairingDesc]

section

open Rep Finsupp

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The inhomogeneous-to-bar comparison evaluates a cochain on a bar basis
element by applying its group-ring coefficient through equivariance. -/
@[simp]
theorem inhomogeneousCochainsIso_hom_apply_single_single
    (A : Rep k G) (n : ℕ) (phi : (inhomogeneousCochains A).X n)
    (f : Fin n → G) (g : G) (r : k) :
    (((inhomogeneousCochainsIso A).hom.f n).hom phi).hom
        (single f (MonoidAlgebra.single g r)) =
      r • A.ρ g (phi f) := by
  change Representation.freeLift A.ρ phi
      (single f (MonoidAlgebra.single g r)) = _
  exact Representation.freeLift_single_single A.ρ f g r phi

/-- The bar-to-standard comparison sends a bar basis element to the basis
element indexed by its successive partial products. -/
@[simp]
theorem barComplex_isoStandardComplex_hom_apply_single
    {n : ℕ} (f : Fin n → G) (g : G) (r : k) :
    ((Rep.barComplex.isoStandardComplex k G).hom.f n).hom
        (single f (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd f) r := by
  change (diagonalSuccIsoFree k G n).inv.hom
      (single f (MonoidAlgebra.single g r)) = _
  simp only [diagonalSuccIsoFree, diagonalSuccIsoTensorTrivial, Iso.trans_inv,
    Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  have step1 : (Hom.hom (leftRegularTensorTrivialIsoFree k G (Fin n → G)).inv)
      (single f (.single g r)) = .single g 1 ⊗ₜ[k] .single f r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single
      f g r
  rw [step1]
  simp only [mkIso_inv, Representation.linearizeOfMulActionIso,
    Representation.Equiv.mk_symm, LinearEquiv.refl_symm,
    ConcreteCategory.hom_ofHom, Action.tensorObj_V, Action.trivial_V,
    Functor.mapIso_inv, tensor_V, tensor_ρ, Iso.symm_inv,
    Functor.Monoidal.μIso_hom, μ_hom, MonoidalCategory.tensorIso_inv,
    Representation.linearizeTrivialIso, hom_tensorHom,
    Representation.IntertwiningMap.tensor_apply,
    Representation.Equiv.coe_toIntertwiningMap,
    Representation.Equiv.mk_apply, LinearEquiv.refl_apply]
  have key₁ := Representation.linearizeMap_single (k := k)
    (Action.diagonalSuccIsoTensorTrivial G n).inv (g, f) ((1 : k) * r)
  have key₂ := Representation.LinearizeMonoidal.μ_apply_single_single
    (k := k) (X := Action.leftRegular G)
    (Y := Action.trivial G (Fin n → G)) g f 1 r
  exact ((congrArg (fun z => (Representation.linearizeMap
      (Action.diagonalSuccIsoTensorTrivial G n).inv) z) key₂).trans key₁).trans (by simp)

/-- The standard-to-bar comparison sends a homogeneous basis simplex to the
bar basis element indexed by its successive quotients, with its initial
vertex as group-ring coefficient. -/
@[simp]
theorem barComplex_isoStandardComplex_inv_apply_single
    {n : ℕ} (u : Fin (n + 1) → G) (r : k) :
    ((Rep.barComplex.isoStandardComplex k G).inv.f n).hom
        (MonoidAlgebra.single u r) =
      single (fun i => (u (Fin.castSucc i))⁻¹ * u i.succ)
        (MonoidAlgebra.single (u 0) r) := by
  let e := Rep.barComplex.isoStandardComplex k G
  have hleft : Function.LeftInverse (e.inv.f n).hom (e.hom.f n).hom := by
    intro z
    change ((e.hom.f n ≫ e.inv.f n).hom z) = z
    rw [← HomologicalComplex.comp_f, e.hom_inv_id]
    rfl
  apply hleft.injective
  have hright (z : (Rep.standardComplex k G).X n) :
      (e.hom.f n).hom ((e.inv.f n).hom z) = z := by
    change ((e.inv.f n ≫ e.hom.f n).hom z) = z
    rw [← HomologicalComplex.comp_f, e.inv_hom_id]
    rfl
  rw [hright]
  rw [barComplex_isoStandardComplex_hom_apply_single]
  rw [Fin.partialProd_left_inv]

/-- Restricting a prefix-product homogeneous simplex to its front face and
transporting back to the bar resolution recovers the initial inhomogeneous
tuple with unit group-ring coefficient. -/
@[simp]
theorem barComplex_frontFace_partialProd_apply_single
    (p q : ℕ) (f : Fin (p + q) → G) :
    ((Rep.barComplex.isoStandardComplex k G).inv.f p).hom
        ((AlgebraicTopology.AlexanderWhitney.frontFace
          (classifyingSpaceUniversalCover G ⋙ Rep.linearization k G)
          (show p + q = p + q by rfl)).hom
          (MonoidAlgebra.single (Fin.partialProd f) 1)) =
      single (fun i => f (Fin.castAdd q i))
        (MonoidAlgebra.single 1 1) := by
  rw [linearizedUniversalCover_frontFace_apply_single]
  rw [barComplex_isoStandardComplex_inv_apply_single]
  congr 2
  · funext i
    have h₁ :
        (AlgebraicTopology.AlexanderWhitney.frontInclusion
          p q (p + q) rfl).toOrderHom i.castSucc =
            (Fin.castAdd q i).castSucc := by
      apply Fin.ext
      simp
    have h₂ :
        (AlgebraicTopology.AlexanderWhitney.frontInclusion
          p q (p + q) rfl).toOrderHom i.succ =
            (Fin.castAdd q i).succ := by
      apply Fin.ext
      simp
    rw [h₁, h₂]
    exact Fin.partialProd_right_inv f (Fin.castAdd q i)

/-- Restricting a prefix-product homogeneous simplex to its back face and
transporting back to the bar resolution recovers the final inhomogeneous
tuple, with the preceding prefix product as group-ring coefficient. -/
@[simp]
theorem barComplex_backFace_partialProd_apply_single
    (p q : ℕ) (f : Fin (p + q) → G) :
    ((Rep.barComplex.isoStandardComplex k G).inv.f q).hom
        ((AlgebraicTopology.AlexanderWhitney.backFace
          (classifyingSpaceUniversalCover G ⋙ Rep.linearization k G)
          (show p + q = p + q by rfl)).hom
          (MonoidAlgebra.single (Fin.partialProd f) 1)) =
      single (fun i => f (Fin.natAdd p i))
        (MonoidAlgebra.single
          (Fin.partialProd f (Fin.natAdd p (0 : Fin (q + 1)))) 1) := by
  rw [linearizedUniversalCover_backFace_apply_single]
  rw [barComplex_isoStandardComplex_inv_apply_single]
  congr 2
  · funext i
    have h₁ :
        (AlgebraicTopology.AlexanderWhitney.backInclusion
          p q (p + q) rfl).toOrderHom i.castSucc =
            (Fin.natAdd p i).castSucc := by
      apply Fin.ext
      simp
      omega
    have h₂ :
        (AlgebraicTopology.AlexanderWhitney.backInclusion
          p q (p + q) rfl).toOrderHom i.succ =
            (Fin.natAdd p i).succ := by
      apply Fin.ext
      simp
      omega
    rw [h₁, h₂]
    exact Fin.partialProd_right_inv f (Fin.natAdd p i)
  · congr 1
    have h₀ :
        (AlgebraicTopology.AlexanderWhitney.backInclusion
          p q (p + q) rfl).toOrderHom 0 =
            Fin.natAdd p (0 : Fin (q + 1)) := by
      apply Fin.ext
      simp
    rw [h₀]

end

/-- The arbitrary-degree cup pairing on linear-Yoneda cochains of the bar
resolution. -/
noncomputable def barCochainCupPairing (A B : Rep k G) :
    HomologicalComplex.CochainGradedPairing
      ((Rep.barComplex k G).linearYonedaObj k A)
      ((Rep.barComplex k G).linearYonedaObj k B)
      ((Rep.barComplex k G).linearYonedaObj k (A ⊗ B)) :=
  HomologicalComplex.linearYonedaCochainGradedPairing k (Rep k G)
    (barComplexDiagonal G k) (𝟙 (A ⊗ B))

/-- Pure-tensor formula for the arbitrary-degree bar cup pairing. -/
@[simp]
theorem barCochainCupPairing_pair_tmul
    (A B : Rep k G) (p q : ℕ)
    (phi : (Rep.barComplex k G).X p ⟶ A)
    (psi : (Rep.barComplex k G).X q ⟶ B) :
    ((barCochainCupPairing G k A B).pair p q).hom
        (phi ⊗ₜ[k] psi) =
      (barComplexDiagonal G k).f (p + q) ≫
        HomologicalComplex.linearYonedaPairingDesc (Rep k G)
          (𝟙 (A ⊗ B)) p q phi psi := by
  set_option backward.isDefEq.respectTransparency false in
  rw [barCochainCupPairing]
  exact HomologicalComplex.linearYonedaCochainPair_tmul
    k (Rep k G) (barComplexDiagonal G k) (𝟙 (A ⊗ B)) p q phi psi

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of the arbitrary-degree bar cup on an unnormalized bar basis
element, expressed through the diagonal and pairing descriptor. -/
theorem barCochainCupPairing_apply_basis
    (A B : Rep k G) (p q : ℕ)
    (phi : (Rep.barComplex k G).X p ⟶ A)
    (psi : (Rep.barComplex k G).X q ⟶ B)
    (g : Fin (p + q) → G) :
    (((inhomogeneousCochainsIso (A ⊗ B)).inv.f (p + q)).hom
      (((barCochainCupPairing G k A B).pair p q).hom
        (phi ⊗ₜ[k] psi))) g =
      ((barComplexDiagonal G k).f (p + q) ≫
        HomologicalComplex.linearYonedaPairingDesc (Rep k G)
          (𝟙 (A ⊗ B)) p q phi psi).hom
        (Finsupp.single g (MonoidAlgebra.single 1 1)) := by
  rw [barCochainCupPairing_pair_tmul]
  rfl

/-- The arbitrary-degree cup pairing transported to inhomogeneous group
cochains. -/
noncomputable def inhomogeneousCupPairing (A B : Rep k G) :
    HomologicalComplex.CochainGradedPairing
      (inhomogeneousCochains A)
      (inhomogeneousCochains B)
      (inhomogeneousCochains (A ⊗ B)) :=
  (barCochainCupPairing G k A B).whisker
    (inhomogeneousCochainsIso A).hom
    (inhomogeneousCochainsIso B).hom
    (inhomogeneousCochainsIso (A ⊗ B)).inv

@[simp]
private lemma moduleHom_comp_apply {M N P : ModuleCat k}
    (f : M ⟶ N) (r : N ⟶ P) (z : M) :
    (f ≫ r).hom z = r.hom (f.hom z) :=
  rfl

@[simp]
private lemma moduleTensorHom_tmul
    {M N P Q : ModuleCat k}
    (f : M ⟶ N) (r : P ⟶ Q) (z : M) (w : P) :
    (f ⊗ₘ r).hom (z ⊗ₜ[k] w) = f.hom z ⊗ₜ[k] r.hom w :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Explicit arbitrary-degree inhomogeneous cup formula.  The right cochain
is acted on by the product of the first `p` group elements. -/
theorem inhomogeneousCupPairing_apply
    (A B : Rep k G) (p q : ℕ)
    (x : (inhomogeneousCochains A).X p)
    (y : (inhomogeneousCochains B).X q)
    (g : Fin (p + q) → G) :
    (((inhomogeneousCupPairing G k A B).pair p q).hom
      (x ⊗ₜ[k] y)) g =
      x (fun i => g (Fin.castAdd q i)) ⊗ₜ[k]
        B.ρ (Fin.partialProd g (Fin.natAdd p (0 : Fin (q + 1))))
          (y (fun i => g (Fin.natAdd p i))) := by
  rw [inhomogeneousCupPairing]
  rw [HomologicalComplex.CochainGradedPairing.whisker_pair]
  rw [moduleHom_comp_apply, moduleHom_comp_apply]
  rw [moduleTensorHom_tmul]
  rw [barCochainCupPairing_apply_basis]
  rw [barComplexDiagonal_comp_linearYonedaPairingDesc]
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_apply,
    Rep.hom_tensorHom, Rep.hom_id,
    Representation.IntertwiningMap.id_apply]
  rw [barComplex_isoStandardComplex_hom_apply_single]
  simp only [one_smul]
  erw [alternatingFaceMapComplex_linearizedUniversalCoverDiagonal_f_apply_single]
  erw [Representation.IntertwiningMap.tensor_apply]
  simp only [Representation.IntertwiningMap.comp_apply]
  erw [barComplex_frontFace_partialProd_apply_single,
    barComplex_backFace_partialProd_apply_single]
  erw [inhomogeneousCochainsIso_hom_apply_single_single,
    inhomogeneousCochainsIso_hom_apply_single_single]
  simp

/-- The arbitrary-degree cup product on group cohomology. -/
noncomputable def cup (A B : Rep k G) (p q : ℕ) :
    groupCohomology A p ⊗ groupCohomology B q ⟶
      groupCohomology (A ⊗ B) (p + q) :=
  (inhomogeneousCupPairing G k A B).pairHomology p q

end groupCohomology
