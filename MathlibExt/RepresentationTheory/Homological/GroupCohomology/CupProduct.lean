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
# Cup products in group cohomology

Let `G` be a group and `k` a commutative ring in the same universe. The simplicial universal
cover of `BG` has homogeneous `n`-simplices `G^(n+1)`, with the diagonal left `G`-action. Its
diagonal, followed by free `k`-linearization and the Alexander–Whitney map, gives a chain
diagonal on the standard resolution and hence on the bar resolution.

For `k`-representations `A` and `B`, this diagonal defines a graded pairing of inhomogeneous
cochains with values in `A ⊗ B`. On cochains of degrees `p` and `q`, its value is
`(x ∪ y)(g₁,…,g_{p+q}) = x(g₁,…,g_p) ⊗ (g₁⋯g_p)·y(g_{p+1},…,g_{p+q})`.
The empty prefix product is `1`. Passing to cohomology gives `H^p(G,A) ⊗ H^q(G,B) → H^{p+q}(G,A ⊗
B)`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace groupCohomology

variable (G : Type u) [Group G]

/-- For a group `G`, the diagonal morphism `EG → EG ⊗ EG` of simplicial `G`-sets sends every
homogeneous simplex `u : Fin (n + 1) → G` to `(u,u)`. The tensor product here is the Cartesian
product with the diagonal `G`-action. -/
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

/-- For a group `G` and a commutative ring `k`, postcomposition with `Rep.linearization k G` sends
a simplicial `G`-set to a simplicial `k`-representation. In each degree it takes the free
`k`-module on the set of simplices, with the induced `G`-action. -/
noncomputable abbrev linearizationOnSimplicialObjects :
    SimplicialObject (Action (Type u) G) ⥤
      SimplicialObject (Rep k G) :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ _ _).obj
    (Rep.linearization k G)

/-- For a group `G` and a commutative ring `k`, the morphism of simplicial representations `k[EG]
→ k[EG] ⊗ k[EG]` is the composite of the free linearization of `EG → EG × EG` with the
oplax-monoidal comparison `k[EG × EG] → k[EG] ⊗ k[EG]`. -/
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

/-- Let `G` be a group, `k` a commutative ring, `n : ℕ`, and `u : Fin (n + 1) → G`. The degree-`n`
linearized diagonal sends the basis vector `MonoidAlgebra.single u 1` to `MonoidAlgebra.single
u 1 ⊗ₜ[k] MonoidAlgebra.single u 1`. -/
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

/-- Let `G` be a group, `k` a commutative ring, `n : ℕ`, and `u : Fin (n + 1) → G`. After applying
the alternating-face-map complex functor to the linearized diagonal, its degree-`n` component
sends `MonoidAlgebra.single u 1` to the pure tensor of two copies of that basis vector. -/
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

/-- Let `G` be a group and `k` a commutative ring. For `p + q = n`, `u : Fin (n + 1) → G`, and `r
: k`, the Alexander–Whitney front-face map sends `single u r` to `single (u ∘ frontInclusion p
q n h) r`. Thus it retains the first `p + 1` vertices and preserves the coefficient `r`. -/
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

/-- Let `G` be a group and `k` a commutative ring. For `p + q = n`, `u : Fin (n + 1) → G`, and `r
: k`, the Alexander–Whitney back-face map sends `single u r` to `single (u ∘ backInclusion p q
n h) r`. Thus it retains the last `q + 1` vertices, starting at vertex `p`, and preserves `r`. -/
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

/-- For a group `G` and a commutative ring `k`, the chain map `Rep.standardComplex k G → tensorObj
(Rep.standardComplex k G) (Rep.standardComplex k G)` is the composite of the alternating-face
complex of the linearized universal-cover diagonal with the Alexander–Whitney chain map. -/
noncomputable def standardComplexDiagonal :
    Rep.standardComplex k G ⟶
      HomologicalComplex.tensorObj
        (Rep.standardComplex k G) (Rep.standardComplex k G) :=
  (AlgebraicTopology.alternatingFaceMapComplex (Rep k G)).map
      (linearizedUniversalCoverDiagonal G k) ≫
    AlgebraicTopology.AlexanderWhitney.alternatingMap
      (classifyingSpaceUniversalCover G ⋙ Rep.linearization k G)
      (classifyingSpaceUniversalCover G ⋙ Rep.linearization k G)

/-- For a group `G` and a commutative ring `k`, let `e : Rep.barComplex k G ≅ Rep.standardComplex
k G` be the standard comparison. The bar chain diagonal is `e.hom ≫ standardComplexDiagonal G
k ≫ tensorHom e.inv e.inv`, with target the total tensor product of two copies of the bar
complex. -/
noncomputable def barComplexDiagonal :
    Rep.barComplex k G ⟶
      HomologicalComplex.tensorObj (Rep.barComplex k G) (Rep.barComplex k G) :=
  (Rep.barComplex.isoStandardComplex k G).hom ≫
    standardComplexDiagonal G k ≫
    HomologicalComplex.tensorHom
      (Rep.barComplex.isoStandardComplex k G).inv
      (Rep.barComplex.isoStandardComplex k G).inv

set_option backward.isDefEq.respectTransparency false in
/-- Let `G` be a group, `k` a commutative ring, `μ : M ⊗ N → P` a morphism of `k`-representations,
`n : ℕ`, and `s : Fin (n + 1)`. For bar cochains `φ : B_s → M` and `ψ : B_{n-s} → N`,
composing the degree-`n` bar diagonal with the `(s,n-s)` pairing descriptor equals the
following composite: transport `B_n` to the standard resolution, apply the linearized
simplicial diagonal and its front/back faces of degrees `s` and `n-s`, apply the transported
cochains `e.inv_s ≫ φ` and `e.inv_{n-s} ≫ ψ`, and then apply `μ`. Here `B` is the bar complex
and `e : B ≅ Rep.standardComplex k G`. -/
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
/-- Let `G` be a group, `k` a commutative ring, and `μ : M ⊗ N → P` a morphism of representations.
For `p,q : ℕ` and bar cochains `φ : B_p → M`, `ψ : B_q → N`, the composite `Δ_B,p+q ≫
linearYonedaPairingDesc μ p q φ ψ` is the standard-resolution front/back Alexander–Whitney
split followed by `(e.inv_p ≫ φ) ⊗ (e.inv_q ≫ ψ)` and `μ`. The input is first transported by
`e.hom_{p+q}`, where `e : B ≅ Rep.standardComplex k G`. -/
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

/-- Let `A` be a `k`-representation of a group `G`, with `k` commutative. For `n : ℕ`, an
inhomogeneous cochain `φ : (Fin n → G) → A`, a tuple `f : Fin n → G`, `g : G`, and `r : k`,
its equivariant bar cochain evaluates `single f (MonoidAlgebra.single g r)` to `r • A.ρ g (φ
f)`. -/
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

/-- For a group `G` and a commutative ring `k`, the degree-`n` bar-to-standard comparison sends
`single f (MonoidAlgebra.single g r)` to `MonoidAlgebra.single (g • Fin.partialProd f) r`, for
`f : Fin n → G`, `g : G`, and `r : k`. The homogeneous tuple is `(g, g f₀, g f₀ f₁, …)`, with
products taken in the displayed order. -/
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

/-- For a group `G` and a commutative ring `k`, the degree-`n` standard-to-bar comparison sends
`MonoidAlgebra.single u r`, for `u : Fin (n + 1) → G`, to the bar basis vector with tuple `i ↦
(u i)⁻¹ * u (i + 1)` and group-ring coefficient `MonoidAlgebra.single (u 0) r`. -/
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

/-- Let `G` be a group, `k` a commutative ring, `p,q : ℕ`, and `f : Fin (p + q) → G`. Apply the
degree-`p` front face to `MonoidAlgebra.single (Fin.partialProd f) 1`, then transport from the
standard to the bar complex. The result is `single (fun i => f (Fin.castAdd q i))
(MonoidAlgebra.single 1 1)`: the initial `p` entries with unit group-ring coefficient. -/
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

/-- Let `G` be a group, `k` a commutative ring, `p,q : ℕ`, and `f : Fin (p + q) → G`. Apply the
degree-`q` back face to `MonoidAlgebra.single (Fin.partialProd f) 1`, then transport to the
bar complex. The result is the bar basis vector with final tuple `i ↦ f (Fin.natAdd p i)` and
group-ring coefficient `single (Fin.partialProd f p) 1`, where the latter group element is the
ordered product of the initial `p` entries. -/
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

/-- For representations `A,B` of a group `G` over a commutative ring `k`, the bar diagonal defines
a graded pairing `Hom_G(B_p,A) ⊗ₖ Hom_G(B_q,B) → Hom_G(B_{p+q},A ⊗ B)`, where `B_n` denotes
the degree-`n` bar-resolution term. The pairing satisfies `d(x ∪ y) = dx ∪ y + (-1)^p x ∪ dy`
for `x` of degree `p`, using the canonical identifications of the resulting degree sums. -/
noncomputable def barCochainCupPairing (A B : Rep k G) :
    HomologicalComplex.CochainGradedPairing
      ((Rep.barComplex k G).linearYonedaObj k A)
      ((Rep.barComplex k G).linearYonedaObj k B)
      ((Rep.barComplex k G).linearYonedaObj k (A ⊗ B)) :=
  HomologicalComplex.linearYonedaCochainGradedPairing k (Rep k G)
    (barComplexDiagonal G k) (𝟙 (A ⊗ B))

/-- Let `G` be a group, `k` a commutative ring, and `A,B` representations. For `p,q : ℕ` and
equivariant bar cochains `φ : (Rep.barComplex k G).X p → A`, `ψ : (Rep.barComplex k G).X q →
B`, the graded cup pairing sends `φ ⊗ₜ[k] ψ` to `barComplexDiagonal G k` in degree `p + q`
followed by `linearYonedaPairingDesc (𝟙 (A ⊗ B)) p q φ ψ`. -/
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

private lemma inhomogeneousCochainsIso_inv_apply_basis
    (A : Rep k G) (n : ℕ) (phi : (Rep.barComplex k G).X n ⟶ A)
    (g : Fin n → G) :
    (((inhomogeneousCochainsIso A).inv.f n).hom phi) g =
      phi.hom (Finsupp.single g (MonoidAlgebra.single 1 1)) := by
  change (Rep.freeLiftLEquiv k G (Fin n → G) A phi) g = _
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Let `A,B` be representations of a group `G` over a commutative ring `k`, and let `φ,ψ` be
equivariant bar cochains of degrees `p,q : ℕ`. Transport their bar cup product to
inhomogeneous cochains and evaluate it at `g : Fin (p + q) → G`. The result is `(Δ_{p+q} ≫
linearYonedaPairingDesc (𝟙 (A ⊗ B)) p q φ ψ)` evaluated at `Finsupp.single g
(MonoidAlgebra.single 1 1)`, where `Δ` is the bar chain diagonal. -/
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
  exact inhomogeneousCochainsIso_inv_apply_basis G k (A ⊗ B) (p + q)
    ((barComplexDiagonal G k).f (p + q) ≫
      HomologicalComplex.linearYonedaPairingDesc (Rep k G)
        (𝟙 (A ⊗ B)) p q phi psi) g

/-- For representations `A,B` of a group `G` over a commutative ring `k`, the cup pairing
`C^p(G,A) ⊗ₖ C^q(G,B) → C^{p+q}(G,A ⊗ B)` is obtained by transporting both inputs to
equivariant bar cochains, applying the bar cup pairing, and transporting the output back. It
satisfies `d(x ∪ y) = dx ∪ y + (-1)^p x ∪ dy` for `x` of degree `p`, with the canonical
degree-sum identifications. -/
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
/-- Let `G` be a group, `k` a commutative ring, `A,B` representations, and `p,q : ℕ`. For
inhomogeneous cochains `x : C^p(G,A)`, `y : C^q(G,B)`, and `g : Fin (p + q) → G`, the cup
value is `x(g₁,…,g_p) ⊗ₜ[k] B.ρ(g₁⋯g_p)(y(g_{p+1},…,g_{p+q}))`. The prefix product uses the
indicated order and equals `1` when `p = 0`. -/
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

/-- For a group `G`, a commutative ring `k`, representations `A,B`, and `p,q : ℕ`, the cup product
is the `k`-linear morphism `H^p(G,A) ⊗ₖ H^q(G,B) → H^{p+q}(G,A ⊗ B)` induced on homology by
the inhomogeneous cochain pairing. Its cochain formula is `x(g₁,…,g_p) ⊗
(g₁⋯g_p)·y(g_{p+1},…,g_{p+q})`. -/
noncomputable def cup (A B : Rep k G) (p q : ℕ) :
    groupCohomology A p ⊗ groupCohomology B q ⟶
      groupCohomology (A ⊗ B) (p + q) :=
  (inhomogeneousCupPairing G k A B).pairHomology p q

end groupCohomology
