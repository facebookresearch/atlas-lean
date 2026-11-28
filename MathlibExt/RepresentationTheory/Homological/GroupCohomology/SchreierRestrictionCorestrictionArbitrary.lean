/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Homology.LinearHomCochainComplex
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupProduct
public import
  MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferArbitraryNaturality
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Restriction-corestriction index formula in every degree

Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, and `T` a right transversal.
Transfer of the subgroup restriction of the basis-valued bar cochain extends to an
endomorphism `E_T` of the bar resolution. Its degree-zero augmentation multiplies by `[G:H]`.

Both `E_T` and `[G:H]` times the identity lift this multiplication on the trivial
representation. The comparison homotopy of the projective bar resolution therefore induces
equal maps on the coefficient Hom complexes. Under the inhomogeneous/bar comparison,
precomposition with `E_T` is restriction followed by transfer.

For every representation `A` and `n : ℕ`, `res_H^G ≫ cor_T = [G:H] • 𝟙` on `H^n(G,A)`.
Restriction is injective whenever the image of the index is a unit in `k`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory
open scoped BigOperators MonoidAlgebra

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

/-- For a group `G`, a finite-index subgroup `H ≤ G`, and a right transversal `T`, the subtype `(T
: Set G)` of representatives has a finite enumeration. This local `Fintype` structure supplies
the finite transfer sums. -/
noncomputable local instance restrictionCorestrictionArbitraryFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- Let `G` be a group, `k` a commutative ring, `n : ℕ`, and `g : Fin n → G`. The element
`barBasis n g` of `(Rep.barComplex k G).X n` is `Finsupp.single g (MonoidAlgebra.single 1 1)`,
the bar basis vector at `g` with unit group-ring coefficient. -/
def barBasis (n : ℕ) (g : Fin n → G) :
    (Rep.barComplex k G).X n :=
  Finsupp.single g (MonoidAlgebra.single 1 1)

theorem freeLift_barBasis (A : Rep k G) (n : ℕ)
    (f : (Fin n → G) → A) (g : Fin n → G) :
    (Rep.freeLift k G A f).hom (barBasis (k := k) n g) = f g := by
  simp [barBasis]

/-- For a group `G`, a commutative ring `k`, and `n : ℕ`, `barBasisCochain n : (Fin n → G) →
(Rep.barComplex k G).X n` sends a tuple `g` to `Finsupp.single g (MonoidAlgebra.single 1 1)`.
It is an inhomogeneous degree-`n` cochain with values in the degree-`n` bar representation. -/
def barBasisCochain (n : ℕ) :
    (Fin n → G) → (Rep.barComplex k G).X n :=
  barBasis (k := k) n

/-- Let `G` be a group, `k` a commutative ring, `n : ℕ`, and `B_n=(Rep.barComplex k G).X n`. The
equivariant linear extension of the basis-valued cochain is the identity: `Rep.freeLift k G
B_n (barBasisCochain n) = 𝟙 B_n`. -/
theorem freeLift_barBasisCochain (n : ℕ) :
    Rep.freeLift k G ((Rep.barComplex k G).X n)
        (barBasisCochain (k := k) (G := G) n) =
      𝟙 ((Rep.barComplex k G).X n) := by
  apply Rep.free_ext k G ((Rep.barComplex k G).X n)
  intro g
  simp [barBasisCochain, barBasis]

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G`, and `n : ℕ`. The function
`restrictedBarBasisCochain n : (Fin n → H) → (Rep.barComplex k G).X n` sends `q` to `barBasis
n (fun i => (q i : G))`, using the subgroup inclusion in every tuple coordinate. -/
def restrictedBarBasisCochain (n : ℕ) :
    (Fin n → H) → (Rep.barComplex k G).X n :=
  fun q ↦ barBasis (k := k) n (fun i ↦ (q i : G))

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G`, and `n : ℕ`. Restricting `barBasisCochain
n` along `H.subtype`, with the identity coefficient morphism on `Res_H((Rep.barComplex k G).X
n)`, gives `restrictedBarBasisCochain n`. This is the equality obtained by applying
`(cochainsMap H.subtype (𝟙 _)).f n` to the ambient cochain. -/
theorem cochainsMap_barBasisCochain (n : ℕ) :
    ((groupCohomology.cochainsMap (Subgroup.subtype H)
      (𝟙 (Rep.res (Subgroup.subtype H)
        ((Rep.barComplex k G).X n)))).f n).hom
        (barBasisCochain (k := k) (G := G) n) =
      restrictedBarBasisCochain (k := k) (G := G) (H := H) n :=
  rfl

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `T` a right transversal, and
`n : ℕ`. Put `B_n=(Rep.barComplex k G).X n`. The endomorphism
`restrictionCorestrictionChainComponent T n : B_n → B_n` is the equivariant linear extension
of `corestrictionCochain B_n T n (restrictedBarBasisCochain n)`. Thus it is obtained by
transferring the subgroup restriction of the basis-valued bar cochain. -/
noncomputable def restrictionCorestrictionChainComponent
    (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ) :
    (Rep.barComplex k G).X n ⟶ (Rep.barComplex k G).X n :=
  Rep.freeLift k G ((Rep.barComplex k G).X n)
    (corestrictionCochain ((Rep.barComplex k G).X n) T n
      (restrictedBarBasisCochain (k := k) (G := G) (H := H) n))

@[simp]
theorem restrictionCorestrictionChainComponent_barBasis
    (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ)
    (g : Fin n → G) :
    (restrictionCorestrictionChainComponent (k := k) T n).hom
        (barBasis (k := k) n g) =
      corestrictionCochain ((Rep.barComplex k G).X n) T n
        (restrictedBarBasisCochain (k := k) (G := G) (H := H) n) g := by
  simp [restrictionCorestrictionChainComponent, barBasis]

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `T` a right transversal, `A
: Rep k G`, `n : ℕ`, and `f : (Fin n → G) → A`. For
`E_{T,n}=restrictionCorestrictionChainComponent T n`, `E_{T,n} ≫ Rep.freeLift k G A f =
Rep.freeLift k G A (corestrictionCochain A T n (fun q => f (fun i => (q i : G))))`. Hence
precomposition represents restriction followed by Schreier transfer on every degree-`n`
cochain. -/
theorem restrictionCorestrictionChainComponent_comp_freeLift
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (n : ℕ) (f : (Fin n → G) → A) :
    restrictionCorestrictionChainComponent (k := k) T n ≫
        Rep.freeLift k G A f =
      Rep.freeLift k G A
        (corestrictionCochain A T n
          (fun q ↦ f (fun i ↦ (q i : G)))) := by
  apply Rep.free_ext k G A
  intro g
  change (Rep.freeLift k G A f).hom
      ((restrictionCorestrictionChainComponent (k := k) T n).hom
        (barBasis (k := k) n g)) =
    (Rep.freeLift k G A
      (corestrictionCochain A T n
        (fun q ↦ f (fun i ↦ (q i : G))))).hom
      (barBasis (k := k) n g)
  rw [restrictionCorestrictionChainComponent_barBasis,
    freeLift_barBasis]
  have h := congrFun
    (corestrictionCochain_naturality (Rep.freeLift k G A f) T n
      (restrictedBarBasisCochain (k := k) (G := G) (H := H) n)) g
  have hbasis :
      (fun q : Fin n → H ↦
        (Rep.freeLift k G A f).hom
          (restrictedBarBasisCochain
            (k := k) (G := G) (H := H) n q)) =
        (fun q ↦ f (fun i ↦ (q i : G))) := by
    funext q
    exact freeLift_barBasis A n f (fun i ↦ (q i : G))
  rw [hbasis] at h
  exact h

/-- Let `G` be a group, `k` a commutative ring, `A : Rep k G`, `n : ℕ`, and `f : (Fin n → G) → A`.
For the bar complex `B`, `B.d (n + 1) n ≫ Rep.freeLift k G A f = Rep.freeLift k G A
((inhomogeneousCochains.d A n).hom f)`. Thus the inhomogeneous differential corresponds to
precomposition by the bar differential. -/
theorem barComplex_d_comp_freeLift
    (A : Rep k G) (n : ℕ) (f : (Fin n → G) → A) :
    (Rep.barComplex k G).d (n + 1) n ≫
        Rep.freeLift k G A f =
      Rep.freeLift k G A
        ((inhomogeneousCochains.d A n).hom f) := by
  apply Rep.free_ext k G A
  intro g
  change (Rep.freeLift k G A f).hom
      (((Rep.barComplex k G).d (n + 1) n).hom
        (barBasis (k := k) (n + 1) g)) =
    (Rep.freeLift k G A
      ((inhomogeneousCochains.d A n).hom f)).hom
      (barBasis (k := k) (n + 1) g)
  rw [freeLift_barBasis]
  rw [Rep.barComplex.d_def]
  simp only [barBasis]
  rw [Rep.barComplex.d_single]
  simp only [map_add, map_sum,
    inhomogeneousCochains.d_hom_apply]
  change Representation.freeLift A.ρ f
      (Finsupp.single (fun i ↦ g i.succ)
        (MonoidAlgebra.single (g 0) 1)) +
      ∑ j : Fin (n + 1), Representation.freeLift A.ρ f
        (Finsupp.single (Fin.contractNth j (fun x y : G ↦ x * y) g)
          (MonoidAlgebra.single 1 ((-1 : k) ^ ((j : ℕ) + 1)))) = _
  simp only [Representation.freeLift_single_single, one_smul,
    map_one, Module.End.one_apply]

/-- Let `G` be a group, `k` a commutative ring, and `n : ℕ`. Put `B_n=(Rep.barComplex k G).X n`.
The cochain `barDifferentialCochain n : (Fin (n + 1) → G) → B_n` is `(inhomogeneousCochains.d
B_n n).hom (barBasisCochain n)`, the inhomogeneous differential of the cochain sending each
degree-`n` tuple to its unit-coefficient bar basis vector. -/
def barDifferentialCochain (n : ℕ) :
    (Fin (n + 1) → G) → (Rep.barComplex k G).X n :=
  (inhomogeneousCochains.d ((Rep.barComplex k G).X n) n).hom
    (barBasisCochain (k := k) (G := G) n)

/-- Let `G` be a group, `k` a commutative ring, and `n : ℕ`. For `B=Rep.barComplex k G`,
`Rep.freeLift k G (B.X n) (barDifferentialCochain n) = B.d (n + 1) n`. Here the cochain being
extended is the inhomogeneous differential of the degree-`n` basis-valued cochain. -/
theorem freeLift_barDifferentialCochain (n : ℕ) :
    Rep.freeLift k G ((Rep.barComplex k G).X n)
        (barDifferentialCochain (k := k) (G := G) n) =
      (Rep.barComplex k G).d (n + 1) n := by
  have h := barComplex_d_comp_freeLift
    ((Rep.barComplex k G).X n) n
      (barBasisCochain (k := k) (G := G) n)
  rw [freeLift_barBasisCochain, Category.comp_id] at h
  exact h.symm

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G`, and `n : ℕ`. With coefficient
`Res_H((Rep.barComplex k G).X n)`, `d_H(restrictedBarBasisCochain n)(q) =
barDifferentialCochain n (fun i => (q i : G))` for `q : Fin (n + 1) → H`. Thus the subgroup
differential is the restriction of the ambient differential cochain. -/
theorem inhomogeneous_d_restrictedBarBasisCochain (n : ℕ) :
    (inhomogeneousCochains.d
      (Rep.res (Subgroup.subtype H) ((Rep.barComplex k G).X n)) n).hom
        (restrictedBarBasisCochain (k := k) (G := G) (H := H) n) =
      fun q ↦ barDifferentialCochain (k := k) (G := G) n
        (fun i ↦ (q i : G)) := by
  funext q
  simp only [restrictedBarBasisCochain, barDifferentialCochain,
    barBasisCochain, inhomogeneousCochains.d_hom_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  have h := Fin.comp_contractNth
    (fun x y : H ↦ x * y) (fun x y : G ↦ x * y)
    (fun x y ↦ (Subgroup.subtype H).map_mul x y) j q
  funext i
  exact congrFun h i

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `T` a right transversal, and
`n : ℕ`. For `E_{T,j}=restrictionCorestrictionChainComponent T j` and `B=Rep.barComplex k G`,
`E_{T,n+1} ≫ B.d (n + 1) n = B.d (n + 1) n ≫ E_{T,n}` as maps `B.X (n + 1) → B.X n`. -/
theorem restrictionCorestrictionChainComponent_comm
    (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ) :
    restrictionCorestrictionChainComponent (k := k) T (n + 1) ≫
        (Rep.barComplex k G).d (n + 1) n =
      (Rep.barComplex k G).d (n + 1) n ≫
        restrictionCorestrictionChainComponent (k := k) T n := by
  let U := restrictedBarBasisCochain
    (k := k) (G := G) (H := H) n
  let C := corestrictionCochain ((Rep.barComplex k G).X n) T n U
  have hrestricted :
      (inhomogeneousCochains.d
        (Rep.res (Subgroup.subtype H) ((Rep.barComplex k G).X n)) n).hom U =
        fun q ↦ barDifferentialCochain (k := k) (G := G) n
          (fun i ↦ (q i : G)) := by
    exact inhomogeneous_d_restrictedBarBasisCochain
      (k := k) (G := G) (H := H) n
  have hcor := corestrictionCochain_d
    ((Rep.barComplex k G).X n) T n U
  rw [hrestricted] at hcor
  calc
    restrictionCorestrictionChainComponent (k := k) T (n + 1) ≫
          (Rep.barComplex k G).d (n + 1) n =
        restrictionCorestrictionChainComponent (k := k) T (n + 1) ≫
          Rep.freeLift k G ((Rep.barComplex k G).X n)
            (barDifferentialCochain (k := k) (G := G) n) := by
      rw [freeLift_barDifferentialCochain]
    _ = Rep.freeLift k G ((Rep.barComplex k G).X n)
        (corestrictionCochain ((Rep.barComplex k G).X n) T (n + 1)
          (fun q ↦ barDifferentialCochain (k := k) (G := G) n
            (fun i ↦ (q i : G)))) :=
      restrictionCorestrictionChainComponent_comp_freeLift
        ((Rep.barComplex k G).X n) T (n + 1)
          (barDifferentialCochain (k := k) (G := G) n)
    _ = Rep.freeLift k G ((Rep.barComplex k G).X n)
        ((inhomogeneousCochains.d ((Rep.barComplex k G).X n) n).hom C) := by
      rw [hcor]
    _ = (Rep.barComplex k G).d (n + 1) n ≫
        Rep.freeLift k G ((Rep.barComplex k G).X n) C := by
      rw [barComplex_d_comp_freeLift]
    _ = (Rep.barComplex k G).d (n + 1) n ≫
        restrictionCorestrictionChainComponent (k := k) T n := rfl

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, and `T` a right transversal.
The chain endomorphism `restrictionCorestrictionBarChain T` of `Rep.barComplex k G` has
component `restrictionCorestrictionChainComponent T n` in every degree `n : ℕ`. Each component
is the equivariant extension of transfer of the subgroup-restricted bar-basis cochain. -/
noncomputable def restrictionCorestrictionBarChain
    (T : H.RightTransversal) [H.FiniteIndex] :
    Rep.barComplex k G ⟶ Rep.barComplex k G where
  f n := restrictionCorestrictionChainComponent (k := k) T n
  comm' i j hij := by
    rcases hij with ⟨rfl⟩
    exact restrictionCorestrictionChainComponent_comm T j

@[simp]
theorem restrictionCorestrictionBarChain_f
    (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ) :
    (restrictionCorestrictionBarChain (k := k) T).f n =
      restrictionCorestrictionChainComponent (k := k) T n :=
  rfl

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, and `T` a right transversal.
The endomorphism `restrictionCorestrictionChain T` of `(Rep.barResolution k G).complex` has
degree-`n` component `restrictionCorestrictionChainComponent T n`. It uses the canonical
identification of this projective-resolution complex with `Rep.barComplex k G`. -/
noncomputable def restrictionCorestrictionChain
    (T : H.RightTransversal) [H.FiniteIndex] :
    (Rep.barResolution k G).complex ⟶
      (Rep.barResolution k G).complex := by
  rw [Rep.barResolution_complex]
  exact restrictionCorestrictionBarChain (k := k) T

@[simp]
theorem restrictionCorestrictionChain_f
    (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ) :
    (restrictionCorestrictionChain (k := k) T).f n =
      restrictionCorestrictionChainComponent (k := k) T n :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- For a group `G` and a commutative ring `k`, the degree-zero augmentation
`ε₀=(Rep.barResolution k G).π.f 0` to the trivial representation sends `barBasis 0 Fin.elim0 =
Finsupp.single Fin.elim0 (MonoidAlgebra.single 1 1)` to `1 : k`. -/
theorem barResolution_augmentation_barBasis_zero :
    ((Rep.barResolution k G).π.f 0).hom
        (barBasis (k := k) 0 Fin.elim0) = (1 : k) := by
  change (Rep.standardComplex.ε k G).hom
    (((Rep.barComplex.isoStandardComplex k G).hom.f 0).hom
      (barBasis (k := k) 0 Fin.elim0)) = 1
  rw [barBasis, barComplex_isoStandardComplex_hom_apply_single]
  simp [Rep.standardComplex.ε]

set_option backward.isDefEq.respectTransparency false in
/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, and `T` a right transversal.
For `E_{T,0}=restrictionCorestrictionChainComponent T 0` and `ε₀=(Rep.barResolution k G).π.f
0`, `ε₀(E_{T,0}(barBasis 0 Fin.elim0)) = (H.index : k)`. -/
theorem restrictionCorestrictionChainComponent_zero_augmentation
    (T : H.RightTransversal) [H.FiniteIndex] :
    ((Rep.barResolution k G).π.f 0).hom
        ((restrictionCorestrictionChainComponent (k := k) T 0).hom
          (barBasis (k := k) 0 Fin.elim0)) = (H.index : k) := by
  rw [restrictionCorestrictionChainComponent_barBasis,
    corestrictionCochain_apply]
  let aug : (Rep.barComplex k G).X 0 ⟶ Rep.trivial k G k :=
    (Rep.barComplex.isoStandardComplex k G).hom.f 0 ≫
      Rep.standardComplex.ε k G
  change aug.hom
      (∑ t : (T : Set G),
        ((Rep.barComplex k G).X 0).ρ (t : G)⁻¹
          (restrictedBarBasisCochain
            (k := k) (G := G) (H := H) 0
            (T.schreierFactorTuple t Fin.elim0))) = (H.index : k)
  rw [map_sum]
  have hterm (t : (T : Set G)) :
      aug.hom
          (((Rep.barComplex k G).X 0).ρ (t : G)⁻¹
            (restrictedBarBasisCochain
              (k := k) (G := G) (H := H) 0
              (T.schreierFactorTuple t Fin.elim0))) = (1 : k) := by
    rw [Rep.hom_comm_apply]
    simp only [Representation.trivial_apply]
    have hbasis :
        restrictedBarBasisCochain
            (k := k) (G := G) (H := H) 0
            (T.schreierFactorTuple t Fin.elim0) =
          barBasis (k := k) 0 Fin.elim0 := by
      unfold restrictedBarBasisCochain
      congr 2
      funext i
      exact Fin.elim0 i
    rw [hbasis]
    dsimp only [aug]
    exact barResolution_augmentation_barBasis_zero
  simp_rw [hterm]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hcard : Fintype.card (T : Set G) = H.index := by
    rw [Fintype.card_eq_nat_card, T.2.card_right]
  rw [hcard]

set_option backward.isDefEq.respectTransparency false in
/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, and `T` a right transversal.
The morphisms from the degree-zero bar term to the trivial representation satisfy
`restrictionCorestrictionChainComponent T 0 ≫ (Rep.barResolution k G).π.f 0 = H.index •
(Rep.barResolution k G).π.f 0`. -/
theorem restrictionCorestrictionChainComponent_zero_comp_augmentation
    (T : H.RightTransversal) [H.FiniteIndex] :
    restrictionCorestrictionChainComponent (k := k) T 0 ≫
        (Rep.barResolution k G).π.f 0 =
      H.index • (Rep.barResolution k G).π.f 0 := by
  apply Rep.free_ext k G (Rep.trivial k G k)
  intro g
  have hg : g = (Fin.elim0 : Fin 0 → G) := Subsingleton.elim _ _
  subst g
  change ((Rep.barResolution k G).π.f 0).hom
      ((restrictionCorestrictionChainComponent (k := k) T 0).hom
        (barBasis (k := k) 0 Fin.elim0)) =
    H.index •
      ((Rep.barResolution k G).π.f 0).hom
        (barBasis (k := k) 0 Fin.elim0)
  rw [restrictionCorestrictionChainComponent_zero_augmentation,
    barResolution_augmentation_barBasis_zero]
  change (H.index : k) = H.index • (1 : k)
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, and `T` a right transversal.
Write `P=Rep.barResolution k G`, `ε=P.π`, and `E_T=restrictionCorestrictionChain T`. Then `E_T
≫ ε = ε ≫ (ChainComplex.single₀ (Rep k G)).map (H.index • 𝟙 (Rep.trivial k G k))`. Thus `E_T`
lifts index multiplication on the trivial representation resolved by `P`. -/
theorem restrictionCorestrictionChain_comp_augmentation
    (T : H.RightTransversal) [H.FiniteIndex] :
    restrictionCorestrictionChain (k := k) T ≫
        (Rep.barResolution k G).π =
      (Rep.barResolution k G).π ≫
        (ChainComplex.single₀ (Rep k G)).map
          (H.index • 𝟙 (Rep.trivial k G k)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
      change restrictionCorestrictionChainComponent (k := k) T 0 ≫
          (Rep.barResolution k G).π.f 0 =
        (Rep.barResolution k G).π.f 0 ≫
          (H.index • 𝟙 (Rep.trivial k G k))
      rw [restrictionCorestrictionChainComponent_zero_comp_augmentation]
      simp
  | succ n => simp

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G`, and `P=Rep.barResolution k G`. Its
augmentation satisfies `(H.index • 𝟙 P.complex) ≫ P.π = P.π ≫ (ChainComplex.single₀ (Rep k
G)).map (H.index • 𝟙 (Rep.trivial k G k))`. This identity holds for any subgroup `H`. -/
theorem indexSMulIdentityChain_comp_augmentation :
    (H.index • 𝟙 (Rep.barResolution k G).complex) ≫
        (Rep.barResolution k G).π =
      (Rep.barResolution k G).π ≫
        (ChainComplex.single₀ (Rep k G)).map
          (H.index • 𝟙 (Rep.trivial k G k)) := by
  rw [Functor.map_nsmul]
  simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
    Category.id_comp]
  rw [(ChainComplex.single₀ (Rep k G)).map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, and `T` a right transversal.
The projective bar resolution `P=Rep.barResolution k G` supplies a chain homotopy from
`restrictionCorestrictionChain T` to `H.index • 𝟙 P.complex`. Both maps lift `H.index • 𝟙` on
the trivial representation through the augmentation of `P`. -/
noncomputable def restrictionCorestrictionChainHomotopy
    (T : H.RightTransversal) [H.FiniteIndex] :
    Homotopy
      (restrictionCorestrictionChain (k := k) T)
      (H.index • 𝟙 (Rep.barResolution k G).complex) :=
  ProjectiveResolution.liftHomotopy
    (H.index • 𝟙 (Rep.trivial k G k))
    (restrictionCorestrictionChain (k := k) T)
    (H.index • 𝟙 (Rep.barResolution k G).complex)
    (restrictionCorestrictionChain_comp_augmentation T)
    (indexSMulIdentityChain_comp_augmentation (H := H))

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `T` a right transversal, and
`A : Rep k G`. The cochain endomorphism `restrictionCorestrictionCochains A T` of `C^*(G,A)`
is `cochainsMap H.subtype (𝟙 (Res_H A)) ≫ corestrictionCochains A T`. In each degree it sends
`f` to the Schreier transfer of the subgroup restriction of `f`. -/
noncomputable def restrictionCorestrictionCochains
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] :
    inhomogeneousCochains A ⟶ inhomogeneousCochains A :=
  groupCohomology.cochainsMap (Subgroup.subtype H)
      (𝟙 (Rep.res (Subgroup.subtype H) A)) ≫
    corestrictionCochains A T

@[simp]
theorem restrictionCorestrictionCochains_f_apply
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (n : ℕ) (f : (Fin n → G) → A) :
    ((restrictionCorestrictionCochains A T).f n).hom f =
      corestrictionCochain A T n
        (fun q ↦ f (fun i ↦ (q i : G))) :=
  rfl

/-- Let `G` be a group, `k` a commutative ring, `A : Rep k G`, and `P` any `ℕ`-indexed chain
complex of representations. The canonical isomorphism identifies
`(linearHomCochainComplexFunctor k (Rep k G) A).obj (Opposite.op P)` with `P.linearYonedaObj k
A`. Their degree-`n` coefficient module is `Hom_{Rep k G}(P.X n,A)`, and the cochain
differential is precomposition by `P.d (n+1) n`. -/
noncomputable def linearHomCochainComplexObjIso
    (A : Rep k G) (P : ChainComplex (Rep k G) ℕ) :
    (HomologicalComplex.linearHomCochainComplexFunctor
      k (Rep k G) A).obj (Opposite.op P) ≅
      P.linearYonedaObj k A :=
  eqToIso (by rfl)

/-- For a group `G`, a commutative ring `k`, and `A : Rep k G`, the canonical equality
`(Rep.barResolution k G).complex = Rep.barComplex k G` induces `barResolutionLinearYonedaIso A
: (Rep.barComplex k G).linearYonedaObj k A ≅ (Rep.barResolution k G).complex.linearYonedaObj k
A`. -/
noncomputable def barResolutionLinearYonedaIso (A : Rep k G) :
    (Rep.barComplex k G).linearYonedaObj k A ≅
      (Rep.barResolution k G).complex.linearYonedaObj k A :=
  eqToIso (congrArg (fun P : ChainComplex (Rep k G) ℕ ↦
    P.linearYonedaObj k A) (Rep.barResolution_complex k G).symm)

/-- For a group `G`, a commutative ring `k`, and `A : Rep k G`, put `P=(Rep.barResolution k
G).complex`. The comparison `inhomogeneousResolutionLinearHomCochainIso A` identifies
`C^*(G,A)` with the linear-Hom cochain complex `L(P,A)`, whose degree-`n` module is `Hom_{Rep
k G}(P.X n,A)`. It composes the inhomogeneous/bar comparison, the bar-resolution linear-Yoneda
comparison, and the inverse linear-Hom/linear-Yoneda identification. -/
noncomputable def inhomogeneousResolutionLinearHomCochainIso
    (A : Rep k G) :
    inhomogeneousCochains A ≅
      (HomologicalComplex.linearHomCochainComplexFunctor
        k (Rep k G) A).obj
          (Opposite.op (Rep.barResolution k G).complex) :=
  inhomogeneousCochainsIso A ≪≫
    barResolutionLinearYonedaIso A ≪≫
    (linearHomCochainComplexObjIso A
      (Rep.barResolution k G).complex).symm

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `T` a right transversal, and
`A : Rep k G`. For `P=(Rep.barResolution k G).complex`, the endomorphism
`restrictionCorestrictionResolutionCochains A T` of `L(P,A)` is the map of the contravariant
linear-Hom functor induced by `(restrictionCorestrictionChain T).op`. Thus each coefficient
cochain precomposes with the corresponding transfer-chain component. -/
noncomputable def restrictionCorestrictionResolutionCochains
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] :
    (HomologicalComplex.linearHomCochainComplexFunctor
      k (Rep k G) A).obj
        (Opposite.op (Rep.barResolution k G).complex) ⟶
      (HomologicalComplex.linearHomCochainComplexFunctor
        k (Rep k G) A).obj
          (Opposite.op (Rep.barResolution k G).complex) :=
  (HomologicalComplex.linearHomCochainComplexFunctor
    k (Rep k G) A).map
      (restrictionCorestrictionChain (k := k) T).op

theorem restrictionCorestrictionResolutionCochains_f_apply
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (n : ℕ)
    (phi : (Rep.barResolution k G).complex.X n ⟶ A) :
    ((restrictionCorestrictionResolutionCochains A T).f n).hom phi =
      (restrictionCorestrictionChain (k := k) T).f n ≫ phi :=
  rfl

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `T` a right transversal, and
`A : Rep k G`. Put `P=(Rep.barResolution k G).complex` and let `L(P,A)` be its linear-Hom
cochain complex. There is a cochain homotopy from `restrictionCorestrictionResolutionCochains
A T` to `H.index • 𝟙 L(P,A)`, induced by the transfer-chain homotopy on `P`. -/
noncomputable def restrictionCorestrictionResolutionCochainsHomotopy
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] :
    Homotopy
      (restrictionCorestrictionResolutionCochains A T)
      (H.index • 𝟙
        ((HomologicalComplex.linearHomCochainComplexFunctor
          k (Rep k G) A).obj
            (Opposite.op (Rep.barResolution k G).complex))) := by
  let h := (restrictionCorestrictionChainHomotopy
    (k := k) T).mapLinearHomCochainComplex k A
  let P := (Rep.barResolution k G).complex
  let F := HomologicalComplex.linearHomCochainComplexFunctor k (Rep k G) A
  have hscalar : F.map (H.index • 𝟙 P).op = H.index • 𝟙 (F.obj (Opposite.op P)) := by
    have hop : (H.index • 𝟙 P).op = H.index • (𝟙 P).op :=
      map_nsmul (CategoryTheory.opHom P P) _ _
    rw [hop, F.map_nsmul]
    change H.index • F.map (𝟙 (Opposite.op P)) = _
    rw [F.map_id]
  rw [hscalar] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `T` a right transversal, and
`A : Rep k G`. For `I_A=inhomogeneousResolutionLinearHomCochainIso A`,
`restrictionCorestrictionCochains A T ≫ I_A.hom = I_A.hom ≫
restrictionCorestrictionResolutionCochains A T`. Thus the inhomogeneous restriction-transfer
operator corresponds to precomposition on Hom cochains of the bar resolution. -/
theorem restrictionCorestrictionCochains_comp_resolutionLinearHomIso_hom
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] :
    restrictionCorestrictionCochains A T ≫
        (inhomogeneousResolutionLinearHomCochainIso A).hom =
      (inhomogeneousResolutionLinearHomCochainIso A).hom ≫
        restrictionCorestrictionResolutionCochains A T := by
  ext n f
  change Rep.freeLift k G A
      (corestrictionCochain A T n
        (fun q ↦ f (fun i ↦ (q i : G)))) =
    restrictionCorestrictionChainComponent (k := k) T n ≫
      Rep.freeLift k G A f
  exact (restrictionCorestrictionChainComponent_comp_freeLift
    A T n f).symm

set_option backward.isDefEq.respectTransparency false in
/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `T` a right transversal, `A
: Rep k G`, and `n : ℕ`. The induced maps on `H^n(G,A)` satisfy
`HomologicalComplex.homologyMap (restrictionCorestrictionCochains A T) n =
HomologicalComplex.homologyMap (H.index • 𝟙 (inhomogeneousCochains A)) n`. -/
theorem homologyMap_restrictionCorestrictionCochains
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ) :
    HomologicalComplex.homologyMap
        (restrictionCorestrictionCochains A T) n =
      HomologicalComplex.homologyMap
        (H.index • 𝟙 (inhomogeneousCochains A)) n := by
  let e := inhomogeneousResolutionLinearHomCochainIso A
  let b := restrictionCorestrictionResolutionCochains A T
  let s := H.index • 𝟙
    ((HomologicalComplex.linearHomCochainComplexFunctor
      k (Rep k G) A).obj
        (Opposite.op (Rep.barResolution k G).complex))
  have hSquare : restrictionCorestrictionCochains A T ≫ e.hom =
      e.hom ≫ b :=
    restrictionCorestrictionCochains_comp_resolutionLinearHomIso_hom A T
  have hBar : HomologicalComplex.homologyMap b n =
      HomologicalComplex.homologyMap s n :=
    (restrictionCorestrictionResolutionCochainsHomotopy
      (H := H) A T).homologyMap_eq n
  have hScalar :
      (H.index • 𝟙 (inhomogeneousCochains A)) ≫ e.hom =
        e.hom ≫ s := by
    dsimp only [s]
    rw [Preadditive.nsmul_comp, Preadditive.comp_nsmul]
    simp only [Category.id_comp, Category.comp_id]
  apply (cancel_mono (HomologicalComplex.homologyMap e.hom n)).mp
  calc
    HomologicalComplex.homologyMap
          (restrictionCorestrictionCochains A T) n ≫
        HomologicalComplex.homologyMap e.hom n =
      HomologicalComplex.homologyMap
        (restrictionCorestrictionCochains A T ≫ e.hom) n := by
          rw [HomologicalComplex.homologyMap_comp]
    _ = HomologicalComplex.homologyMap (e.hom ≫ b) n := by
      rw [hSquare]
    _ = HomologicalComplex.homologyMap e.hom n ≫
        HomologicalComplex.homologyMap b n := by
      rw [HomologicalComplex.homologyMap_comp]
    _ = HomologicalComplex.homologyMap e.hom n ≫
        HomologicalComplex.homologyMap s n := by rw [hBar]
    _ = HomologicalComplex.homologyMap (e.hom ≫ s) n := by
      rw [HomologicalComplex.homologyMap_comp]
    _ = HomologicalComplex.homologyMap
        ((H.index • 𝟙 (inhomogeneousCochains A)) ≫ e.hom) n := by
      rw [hScalar]
    _ = HomologicalComplex.homologyMap
          (H.index • 𝟙 (inhomogeneousCochains A)) n ≫
        HomologicalComplex.homologyMap e.hom n := by
      rw [HomologicalComplex.homologyMap_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `T` a right transversal, `A
: Rep k G`, and `n : ℕ`. Then `map H.subtype (𝟙 (Res_H A)) n ≫ corestrictionOfRightTransversal
A T n = H.index • 𝟙 (H^n(G,A))`. The composite is restriction to `H` followed by the
cohomology map induced by Schreier transfer for `T`. -/
theorem corestrictionOfRightTransversal_restriction
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ) :
    groupCohomology.map (Subgroup.subtype H)
        (𝟙 (Rep.res (Subgroup.subtype H) A)) n ≫
      corestrictionOfRightTransversal A T n =
        H.index • 𝟙 (groupCohomology A n) := by
  change HomologicalComplex.homologyMap
      (groupCohomology.cochainsMap (Subgroup.subtype H)
        (𝟙 (Rep.res (Subgroup.subtype H) A))) n ≫
    HomologicalComplex.homologyMap (corestrictionCochains A T) n = _
  rw [← HomologicalComplex.homologyMap_comp]
  change HomologicalComplex.homologyMap
      (restrictionCorestrictionCochains A T) n = _
  change HomologicalComplex.homologyMap
      (restrictionCorestrictionCochains A T) n =
    H.index • 𝟙 ((inhomogeneousCochains A).homology n)
  rw [homologyMap_restrictionCorestrictionCochains]
  change (HomologicalComplex.homologyFunctor (ModuleCat k)
    (ComplexShape.up ℕ) n).map (H.index • 𝟙 (inhomogeneousCochains A)) = _
  rw [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id]
  rfl

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `T` a right transversal, `A
: Rep k G`, and `n : ℕ`. For `x ∈ H^n(G,A)`, `corestrictionOfRightTransversal A T n (map
H.subtype (𝟙 (Res_H A)) n x) = (H.index : k) • x`. -/
theorem corestrictionOfRightTransversal_restriction_apply
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ)
    (x : groupCohomology A n) :
    corestrictionOfRightTransversal A T n
        (groupCohomology.map (Subgroup.subtype H)
          (𝟙 (Rep.res (Subgroup.subtype H) A)) n x) =
      (H.index : k) • x := by
  have h := ConcreteCategory.congr_hom
    (corestrictionOfRightTransversal_restriction A T n) x
  change corestrictionOfRightTransversal A T n
      (groupCohomology.map (Subgroup.subtype H)
        (𝟙 (Rep.res (Subgroup.subtype H) A)) n x) =
    H.index • x at h
  simpa only [Nat.cast_smul_eq_nsmul] using h

/-- Let `G` be a group, `k` a commutative ring, `H ≤ G` finite index, `A : Rep k G`, and `n : ℕ`.
If `IsUnit (H.index : k)`, then restriction `map H.subtype (𝟙 (Res_H A)) n : H^n(G,A) →
H^n(H,Res_H A)` is injective. -/
theorem restriction_injective_of_isUnit_index
    (A : Rep k G) [H.FiniteIndex] (n : ℕ)
    (hindex : IsUnit (H.index : k)) :
    Function.Injective
      (groupCohomology.map (Subgroup.subtype H)
        (𝟙 (Rep.res (Subgroup.subtype H) A)) n) := by
  let T : H.RightTransversal := default
  intro x y hxy
  apply hindex.smul_left_cancel.mp
  rw [← corestrictionOfRightTransversal_restriction_apply A T n x,
    ← corestrictionOfRightTransversal_restriction_apply A T n y, hxy]

end groupCohomology
