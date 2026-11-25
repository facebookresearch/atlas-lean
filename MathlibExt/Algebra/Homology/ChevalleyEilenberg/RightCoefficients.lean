/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Category.RightLieModuleCat.Basic
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.LieNaturalityULift
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoefficientComparison
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.Canonical
public import Mathlib.Algebra.Lie.Abelian

/-!
# Chevalley–Eilenberg chains with right Lie coefficients

For a Lie algebra L over a commutative ring R and a right Lie module M, chains in degree n are
`M ⊗[R] (⋀[R]^n L)`. Tensor symmetry identifies this complex with the left-coefficient complex
for the action `[x,m] = -(m · x)`.

The action term has sign `(-1)^i` for indices starting at zero. In degree one the boundary is
`m · x`, and the degree-two bracket contribution is `-m ⊗ [x,y]`. Compatible Lie and
coefficient maps induce chain maps, with universe-lift comparisons preserving the ground-ring
action.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct BigOperators

universe u v v' v'' w w' w'' z

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

/-- The coefficient-first chain object for a right Lie module. -/
abbrev rightCoefficientChainObject (M : RightLieModuleCat.{w} R L) (n : ℕ) :
    ModuleCat.{max u v w} R := ModuleCat.of R (M ⊗[R] (⋀[R]^n L))

/-- Tensor commutation identifies the right object with the left object. -/
def rightCoefficientDegreeEquiv (M : RightLieModuleCat.{w} R L) (n : ℕ) :
    (M ⊗[R] (⋀[R]^n L)) ≃ₗ[R]
      ((⋀[R]^n L) ⊗[R] RightLieModuleCat.toLeft M) :=
  TensorProduct.comm R M (⋀[R]^n L)

/-- The right differential is the transport of the left CE differential. -/
def rightCoefficientDifferential (M : RightLieModuleCat.{w} R L) (n : ℕ) :
    (M ⊗[R] (⋀[R]^(n + 1) L)) →ₗ[R] (M ⊗[R] (⋀[R]^n L)) :=
  (rightCoefficientDegreeEquiv R L M n).symm.toLinearMap.comp
    ((coefficientDifferential R L (RightLieModuleCat.toLeft M) n).comp
      (rightCoefficientDegreeEquiv R L M (n + 1)).toLinearMap)

/-- Tensor coordinates expose the exact boundary used by the right differential. -/
theorem rightCoefficientDifferential_equiv (M : RightLieModuleCat.{w} R L) (n : ℕ)
    (p : M ⊗[R] (⋀[R]^(n + 1) L)) :
    rightCoefficientDegreeEquiv R L M n (rightCoefficientDifferential R L M n p) =
      coefficientDifferential R L (RightLieModuleCat.toLeft M) n
        (rightCoefficientDegreeEquiv R L M (n + 1) p) :=
  (rightCoefficientDegreeEquiv R L M n).apply_symm_apply _

/-- The inherited square-zero equation survives the tensor-coordinate transport. -/
theorem rightCoefficientDifferential_comp_differential
    (M : RightLieModuleCat.{w} R L) (n : ℕ) :
    (rightCoefficientDifferential R L M n).comp
        (rightCoefficientDifferential R L M (n + 1)) = 0 := by
  apply LinearMap.ext
  intro p
  let e₀ := rightCoefficientDegreeEquiv R L M n
  let e₁ := rightCoefficientDegreeEquiv R L M (n + 1)
  let e₂ := rightCoefficientDegreeEquiv R L M (n + 2)
  let d₀ := coefficientDifferential R L (RightLieModuleCat.toLeft M) n
  let d₁ := coefficientDifferential R L (RightLieModuleCat.toLeft M) (n + 1)
  change e₀.symm (d₀ (e₁ (e₁.symm (d₁ (e₂ p))))) = 0
  rw [e₁.apply_symm_apply]
  have h : d₀ (d₁ (e₂ p)) = 0 :=
    LinearMap.congr_fun
      (coefficientDifferential_comp_differential R L (RightLieModuleCat.toLeft M) n)
      (e₂ p)
  rw [h]
  exact e₀.symm.toLinearMap.map_zero

/-- The coefficient-first complex, formed by the chain-complex constructor. -/
def rightCoefficientComplex (M : RightLieModuleCat.{w} R L) :
    ChainComplex (ModuleCat.{max u v w} R) ℕ :=
  ChainComplex.of (rightCoefficientChainObject R L M)
    (fun n => ModuleCat.ofHom (rightCoefficientDifferential R L M n))
    (fun n => by
      rw [← ModuleCat.ofHom_comp, rightCoefficientDifferential_comp_differential,
        ModuleCat.ofHom_zero])

@[simp]
theorem rightCoefficientComplex_X (M : RightLieModuleCat.{w} R L) (n : ℕ) :
    (rightCoefficientComplex R L M).X n = rightCoefficientChainObject R L M n := rfl

@[simp]
theorem rightCoefficientComplex_d_succ (M : RightLieModuleCat.{w} R L) (n : ℕ) :
    (rightCoefficientComplex R L M).d (n + 1) n =
      ModuleCat.ofHom (rightCoefficientDifferential R L M n) := by
  simp only [rightCoefficientComplex, ChainComplex.of_d]

theorem rightCoefficientComplex_d_eq_zero (M : RightLieModuleCat.{w} R L)
    (i j : ℕ) (h : i ≠ j + 1) :
    (rightCoefficientComplex R L M).d i j = 0 :=
  ChainComplex.of_d_ne (rightCoefficientChainObject R L M)
    (fun n => ModuleCat.ofHom (rightCoefficientDifferential R L M n)) h

/-- The coefficient-first complex is canonically isomorphic to the left CE complex. -/
def rightCoefficientComplexIso (M : RightLieModuleCat.{w} R L) :
    rightCoefficientComplex R L M ≅ coefficientComplex R L (RightLieModuleCat.toLeft M) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (rightCoefficientDegreeEquiv R L M n).toModuleIso) ?_
  intro i j hij
  change j + 1 = i at hij
  subst i
  rw [rightCoefficientComplex_d_succ, coefficientComplex_d_succ]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro p
  exact (rightCoefficientDifferential_equiv R L M j p).symm

/-- The comparison interchanges the two pure tensor factors. -/
theorem rightCoefficientComplexIso_hom_f_tmul (M : RightLieModuleCat.{w} R L)
    (n : ℕ) (m : M) (a : ⋀[R]^n L) :
    ((rightCoefficientComplexIso R L M).hom.f n).hom (m ⊗ₜ[R] a) = a ⊗ₜ[R] m := by
  change TensorProduct.comm R M.carrier (⋀[R]^n L) (m ⊗ₜ[R] a) = a ⊗ₜ[R] m
  exact TensorProduct.comm_tmul R M.carrier (⋀[R]^n L) m a

theorem rightCoefficientComplexIso_inv_f_tmul (M : RightLieModuleCat.{w} R L)
    (n : ℕ) (a : ⋀[R]^n L) (m : M) :
    ((rightCoefficientComplexIso R L M).inv.f n).hom (a ⊗ₜ[R] m) = m ⊗ₜ[R] a := by
  change (TensorProduct.comm R M.carrier (⋀[R]^n L)).symm (a ⊗ₜ[R] m) = m ⊗ₜ[R] a
  exact TensorProduct.comm_symm_tmul R M.carrier (⋀[R]^n L) m a

/-- Right coefficients have the positive action in degree one. -/
theorem rightCoefficientDifferential_ι_tmul (M : RightLieModuleCat.{w} R L)
    (m : M) (x : L) :
    rightCoefficientDifferential R L M 0
        (m ⊗ₜ[R] exteriorPower.ιMulti R 1 (fun _ => x)) =
      M.action x m ⊗ₜ[R] exteriorPower.ιMulti R 0 Fin.elim0 := by
  change (rightCoefficientDegreeEquiv R L M 0).symm
      (coefficientDifferential R L (RightLieModuleCat.toLeft M) 0
        (exteriorPower.ιMulti R 1 (fun _ => x) ⊗ₜ[R] m)) = _
  rw [coefficientDifferential_ι_tmul, RightLieModuleCat.toLeft_lie]
  let a₀ : ⋀[R]^0 L := exteriorPower.ιMulti R 0 Fin.elim0
  let z : RightLieModuleCat.toLeft M := M.action x m
  have hTensor : -(a₀ ⊗ₜ[R] (-z)) = a₀ ⊗ₜ[R] z := by
    exact (congrArg (fun t : (⋀[R]^0 L) ⊗[R] RightLieModuleCat.toLeft M => -t)
      (TensorProduct.tmul_neg a₀ z)).trans (neg_neg (a₀ ⊗ₜ[R] z))
  change (rightCoefficientDegreeEquiv R L M 0).symm (-(a₀ ⊗ₜ[R] (-z))) =
    M.action x m ⊗ₜ[R] a₀
  rw [hTensor]
  exact TensorProduct.comm_symm_tmul R M.carrier (⋀[R]^0 L) (M.action x m) a₀

/-- Degree-zero coefficient coordinates detect the positive right action. -/
theorem rightCoefficientDifferential_zero_coordinate (M : RightLieModuleCat.{w} R L)
    (m : M) (x : L) :
    coefficientZeroEquiv R L (RightLieModuleCat.toLeft M)
        (rightCoefficientDegreeEquiv R L M 0
          (rightCoefficientDifferential R L M 0
            (m ⊗ₜ[R] exteriorPower.ιMulti R 1 (fun _ => x)))) = M.action x m := by
  rw [rightCoefficientDifferential_ι_tmul]
  change coefficientZeroEquiv R L (RightLieModuleCat.toLeft M)
      (exteriorPower.ιMulti R 0 Fin.elim0 ⊗ₜ[R] M.action x m) = _
  exact coefficientZeroEquiv_ι_tmul R L (RightLieModuleCat.toLeft M) (M.action x m)

/-- The all-degree formula has the unchanged bracket term and zero-based right-action signs. -/
theorem rightCoefficientDifferential_apply_ιMulti_tmul
    (M : RightLieModuleCat.{w} R L) (n : ℕ) (xs : Fin (n + 1) → L) (m : M) :
    rightCoefficientDifferential R L M n
        (m ⊗ₜ[R] exteriorPower.ιMulti R (n + 1) xs) =
      m ⊗ₜ[R] differential R L n (exteriorPower.ιMulti R (n + 1) xs) +
        ∑ i : Fin (n + 1), (-1 : R) ^ i.val •
          (M.action (xs i) m ⊗ₜ[R] exteriorPower.ιMulti R n (xs ∘ i.succAbove)) := by
  change (rightCoefficientDegreeEquiv R L M n).symm
      (coefficientDifferential R L (RightLieModuleCat.toLeft M) n
        (exteriorPower.ιMulti R (n + 1) xs ⊗ₜ[R] m)) = _
  rw [coefficientDifferential_apply_ιMulti_tmul]
  simp only [map_add, map_sum, map_smul, rightCoefficientDegreeEquiv,
    TensorProduct.comm_symm, TensorProduct.comm_tmul, RightLieModuleCat.toLeft_lie]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [TensorProduct.neg_tmul, smul_neg, pow_succ, mul_neg, mul_one,
    neg_smul, neg_neg]

/-- The bracket term has exactly the signed bracket-boundary presentation. -/
theorem rightCoefficientDifferential_apply_ιMulti_tmul_bracket
    (M : RightLieModuleCat.{w} R L) (n : ℕ) (xs : Fin (n + 1) → L) (m : M) :
    rightCoefficientDifferential R L M n
        (m ⊗ₜ[R] exteriorPower.ιMulti R (n + 1) xs) =
      m ⊗ₜ[R] bracketBoundary R L n xs +
        ∑ i : Fin (n + 1), (-1 : R) ^ i.val •
          (M.action (xs i) m ⊗ₜ[R] exteriorPower.ιMulti R n (xs ∘ i.succAbove)) := by
  rw [rightCoefficientDifferential_apply_ιMulti_tmul, differential_apply_ιMulti]

/-- Degree two retains both ordered action terms and the negative bracket term. -/
theorem rightCoefficientDifferential_two_coordinate
    (M : RightLieModuleCat.{w} R L) (m : M) (x y : L) :
    (exteriorPower.oneEquiv R L).lTensor M
        (rightCoefficientDifferential R L M 1
          (m ⊗ₜ[R] exteriorPower.ιMulti R 2 ![x, y])) =
      (M.action x m ⊗ₜ[R] y) - (M.action y m ⊗ₜ[R] x) - (m ⊗ₜ[R] ⁅x, y⁆) := by
  have hBracket : differential R L 1 (exteriorPower.ιMulti R 2 ![x, y]) =
      -(exteriorPower.ιMulti R 1 (fun _ => ⁅x, y⁆)) := by
    apply Subtype.ext
    simpa only [differential_coe, exteriorPower.ιMulti_apply_coe,
      ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.tail_cons, mul_one,
      Submodule.coe_neg] using boundary_ι_mul_ι R L x y
  have hDelete₀ : ![x, y] ∘ (0 : Fin 2).succAbove = (fun _ : Fin 1 => y) := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  have hDelete₁ : ![x, y] ∘ (1 : Fin 2).succAbove = (fun _ : Fin 1 => x) := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  have hAction :
      (∑ i : Fin 2, (-1 : R) ^ i.val •
        (M.action (![x, y] i) m ⊗ₜ[R] exteriorPower.ιMulti R 1 (![x, y] ∘ i.succAbove))) =
      M.action x m ⊗ₜ[R] exteriorPower.ιMulti R 1 (fun _ => y) -
        M.action y m ⊗ₜ[R] exteriorPower.ιMulti R 1 (fun _ => x) := by
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul,
      hDelete₀, hDelete₁, Matrix.cons_val_zero, Matrix.cons_val_one, sub_eq_add_neg]
  rw [rightCoefficientDifferential_apply_ιMulti_tmul, hBracket, hAction]
  simp only [TensorProduct.tmul_neg, map_add, map_sub, map_neg,
    LinearEquiv.lTensor_tmul, exteriorPower.oneEquiv_ιMulti]
  abel

section LieMaps

variable {L' : Type v'} [LieRing L'] [LieAlgebra R L']
variable (f : L →ₗ⁅R⁆ L')
variable (M : RightLieModuleCat.{w} R L) (N : RightLieModuleCat.{w'} R L')

/-- A right coefficient map establishes the restricted left coefficient map. -/
def rightCoefficientLieMapToLeft (g : RightLieModuleCat.HomOver f M N) :
    RightLieModuleCat.toLeft M →ₗ⁅R,L⁆
      LieModuleCat.restrictObj f (RightLieModuleCat.toLeft N) where
  toLinearMap := g.toLinearMap
  map_lie' := by
    intro x m
    change g.toLinearMap (-(M.action x m)) = -(N.action (f x) (g.toLinearMap m))
    rw [g.toLinearMap.map_neg]
    exact congrArg Neg.neg (g.map_action x m)

theorem rightCoefficientLieMapToLeft_apply (g : RightLieModuleCat.HomOver f M N) (m : M) :
    rightCoefficientLieMapToLeft R L f M N g m = g.toLinearMap m := rfl

/-- The degree map applies the coefficient map first and the Lie exterior map second. -/
def rightCoefficientLieDegreeMap (g : RightLieModuleCat.HomOver f M N) (n : ℕ) :
    (M ⊗[R] (⋀[R]^n L)) →ₗ[R] (N ⊗[R] (⋀[R]^n L')) :=
  TensorProduct.map g.toLinearMap (exteriorPower.map n f.toLinearMap)

@[simp]
theorem rightCoefficientLieDegreeMap_tmul (g : RightLieModuleCat.HomOver f M N)
    (n : ℕ) (m : M) (a : ⋀[R]^n L) :
    rightCoefficientLieDegreeMap R L f M N g n (m ⊗ₜ[R] a) =
      g.toLinearMap m ⊗ₜ[R] exteriorPower.map n f.toLinearMap a := by
  simp only [rightCoefficientLieDegreeMap, TensorProduct.map_tmul]

/-- Linear right degree maps compose for independently sized Lie and coefficient carriers. -/
theorem rightCoefficientLieDegreeMap_comp
    {L'' : Type v''} [LieRing L''] [LieAlgebra R L'']
    (h : L' →ₗ⁅R⁆ L'') (P : RightLieModuleCat.{w''} R L'')
    (g : RightLieModuleCat.HomOver f M N) (k : RightLieModuleCat.HomOver h N P)
    (n : ℕ) :
    (rightCoefficientLieDegreeMap R L' h N P k n).comp
        (rightCoefficientLieDegreeMap R L f M N g n) =
      rightCoefficientLieDegreeMap R L (h.comp f) M P
        (RightLieModuleCat.HomOver.comp k g) n := by
  apply TensorProduct.ext'
  intro m a
  rw [LinearMap.comp_apply, rightCoefficientLieDegreeMap_tmul,
    rightCoefficientLieDegreeMap_tmul, rightCoefficientLieDegreeMap_tmul,
    RightLieModuleCat.HomOver.comp_apply, LieHom.toLinearMap_comp,
    exteriorPower.map_comp, LinearMap.comp_apply]

/-- Tensor commutation relates the right degree map to the left degree map. -/
theorem rightCoefficientLieDegreeMap_equiv (g : RightLieModuleCat.HomOver f M N)
    (n : ℕ) (p : M ⊗[R] (⋀[R]^n L)) :
    rightCoefficientDegreeEquiv R L' N n (rightCoefficientLieDegreeMap R L f M N g n p) =
      coefficientLieDegreeMap R L f (RightLieModuleCat.toLeft M)
        (RightLieModuleCat.toLeft N) (rightCoefficientLieMapToLeft R L f M N g) n
        (rightCoefficientDegreeEquiv R L M n p) := by
  induction p using TensorProduct.inductionOn with
  | tmul m a =>
      let gLeft := rightCoefficientLieMapToLeft R L f M N g
      let F := coefficientLieDegreeMap R L f
        (RightLieModuleCat.toLeft M) (RightLieModuleCat.toLeft N) gLeft n
      have hPoint : F (a ⊗ₜ[R] m) =
          exteriorPower.map n f.toLinearMap a ⊗ₜ[R] (g.toLinearMap m : RightLieModuleCat.toLeft N) :=
        (coefficientLieDegreeMap_tmul R L f
          (RightLieModuleCat.toLeft M) (RightLieModuleCat.toLeft N) gLeft n a m).trans
          (congrArg (fun y : RightLieModuleCat.toLeft N =>
            exteriorPower.map n f.toLinearMap a ⊗ₜ[R] y)
            (rightCoefficientLieMapToLeft_apply R L f M N g m))
      have hM : rightCoefficientDegreeEquiv R L M n (m ⊗ₜ[R] a) = a ⊗ₜ[R] m :=
        TensorProduct.comm_tmul R M.carrier (⋀[R]^n L) m a
      have hLeft : rightCoefficientDegreeEquiv R L' N n
          (rightCoefficientLieDegreeMap R L f M N g n (m ⊗ₜ[R] a)) =
          exteriorPower.map n f.toLinearMap a ⊗ₜ[R]
            (g.toLinearMap m : RightLieModuleCat.toLeft N) :=
        (congrArg (rightCoefficientDegreeEquiv R L' N n)
          (rightCoefficientLieDegreeMap_tmul R L f M N g n m a)).trans
          (TensorProduct.comm_tmul R N.carrier (⋀[R]^n L')
            (g.toLinearMap m) (exteriorPower.map n f.toLinearMap a))
      exact hLeft.trans ((congrArg F hM).trans hPoint).symm
  | add p q hp hq => simp only [map_add, hp, hq]

/-- Arbitrary compatible coefficient and Lie maps intertwine the transported differential. -/
theorem rightCoefficientLieDifferential_naturality
    (g : RightLieModuleCat.HomOver f M N) (n : ℕ) :
    (rightCoefficientLieDegreeMap R L f M N g n).comp
        (rightCoefficientDifferential R L M n) =
      (rightCoefficientDifferential R L' N n).comp
        (rightCoefficientLieDegreeMap R L f M N g (n + 1)) := by
  apply LinearMap.ext
  intro p
  apply (rightCoefficientDegreeEquiv R L' N n).injective
  change rightCoefficientDegreeEquiv R L' N n
      (rightCoefficientLieDegreeMap R L f M N g n (rightCoefficientDifferential R L M n p)) =
    rightCoefficientDegreeEquiv R L' N n
      (rightCoefficientDifferential R L' N n
        (rightCoefficientLieDegreeMap R L f M N g (n + 1) p))
  rw [rightCoefficientLieDegreeMap_equiv, rightCoefficientDifferential_equiv,
    rightCoefficientDifferential_equiv, rightCoefficientLieDegreeMap_equiv]
  exact LinearMap.congr_fun
    (coefficientLieDifferential_naturality R L f (RightLieModuleCat.toLeft M)
      (RightLieModuleCat.toLeft N) (rightCoefficientLieMapToLeft R L f M N g) n)
    (rightCoefficientDegreeEquiv R L M (n + 1) p)

end LieMaps

section NativeLieMaps

variable {L' : Type v} [LieRing L'] [LieAlgebra R L']
variable (f : L →ₗ⁅R⁆ L')
variable (M : RightLieModuleCat.{w} R L) (N : RightLieModuleCat.{w} R L')

/-- The right CE map is the left map conjugated by the tensor isomorphisms. -/
def rightCoefficientLieComplexMap (g : RightLieModuleCat.HomOver f M N) :
    rightCoefficientComplex R L M ⟶ rightCoefficientComplex R L' N :=
  (rightCoefficientComplexIso R L M).hom ≫
    coefficientLieComplexMap R L f (RightLieModuleCat.toLeft M)
      (RightLieModuleCat.toLeft N) (rightCoefficientLieMapToLeft R L f M N g) ≫
        (rightCoefficientComplexIso R L' N).inv

/-- The chain component has the coefficient-first pure tensor formula. -/
theorem rightCoefficientLieComplexMap_f_tmul (g : RightLieModuleCat.HomOver f M N)
    (n : ℕ) (m : M) (a : ⋀[R]^n L) :
    ((rightCoefficientLieComplexMap R L f M N g).f n).hom (m ⊗ₜ[R] a) =
      g.toLinearMap m ⊗ₜ[R] exteriorPower.map n f.toLinearMap a := by
  change (rightCoefficientDegreeEquiv R L' N n).symm
    (coefficientLieDegreeMap R L f (RightLieModuleCat.toLeft M)
      (RightLieModuleCat.toLeft N) (rightCoefficientLieMapToLeft R L f M N g) n
      (rightCoefficientDegreeEquiv R L M n (m ⊗ₜ[R] a))) = _
  let e := rightCoefficientDegreeEquiv R L' N n
  exact (congrArg e.symm
    (rightCoefficientLieDegreeMap_equiv R L f M N g n (m ⊗ₜ[R] a)).symm).trans
    ((e.symm_apply_apply _).trans (rightCoefficientLieDegreeMap_tmul R L f M N g n m a))

/-- The identity Lie and coefficient maps give the identity chain map. -/
theorem rightCoefficientLieComplexMap_id :
    rightCoefficientLieComplexMap R L (LieHom.id : L →ₗ⁅R⁆ L) M M (𝟙 M) =
      𝟙 (rightCoefficientComplex R L M) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m a
  change ((rightCoefficientLieComplexMap R L LieHom.id M M (𝟙 M)).f n).hom
      (m ⊗ₜ[R] a) = m ⊗ₜ[R] a
  rw [rightCoefficientLieComplexMap_f_tmul]
  change m ⊗ₜ[R] exteriorPower.map n (LinearMap.id : L →ₗ[R] L) a = m ⊗ₜ[R] a
  rw [exteriorPower.map_id]
  rfl

/-- Joint Lie and right-coefficient maps compose on the chain complexes. -/
theorem rightCoefficientLieComplexMap_comp
    {L'' : Type v} [LieRing L''] [LieAlgebra R L'']
    (h : L' →ₗ⁅R⁆ L'') (P : RightLieModuleCat.{w} R L'')
    (g : RightLieModuleCat.HomOver f M N) (k : RightLieModuleCat.HomOver h N P) :
    rightCoefficientLieComplexMap R L f M N g ≫
        rightCoefficientLieComplexMap R L' h N P k =
      rightCoefficientLieComplexMap R L (h.comp f) M P
        (RightLieModuleCat.HomOver.comp k g) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m a
  change ((rightCoefficientLieComplexMap R L' h N P k).f n).hom
    (((rightCoefficientLieComplexMap R L f M N g).f n).hom (m ⊗ₜ[R] a)) =
      ((rightCoefficientLieComplexMap R L (h.comp f) M P
        (RightLieModuleCat.HomOver.comp k g)).f n).hom (m ⊗ₜ[R] a)
  rw [rightCoefficientLieComplexMap_f_tmul, rightCoefficientLieComplexMap_f_tmul,
    rightCoefficientLieComplexMap_f_tmul, RightLieModuleCat.HomOver.comp_apply,
    LieHom.toLinearMap_comp, exteriorPower.map_comp, LinearMap.comp_apply]

end NativeLieMaps

/-- Prolongation of the right coefficient complex to a common module universe. -/
def rightCoefficientComplexULift (M : RightLieModuleCat.{w} R L) :
    ChainComplex (ModuleCat.{max u v w z} R) ℕ :=
  ((ModuleCat.uliftFunctor.{z, max u v w} R).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (rightCoefficientComplex R L M)

/-- The prolonged degree object is the lift of the coefficient-first tensor. -/
theorem rightCoefficientComplexULift_X
    (M : RightLieModuleCat.{w} R L) (n : ℕ) :
    (rightCoefficientComplexULift.{u,v,w,z} R L M).X n =
      ModuleCat.of R (ULift.{z} (M ⊗[R] (⋀[R]^n L))) := rfl

/-- Prolonging the tensor isomorphism gives the lifted left CE model. -/
def rightCoefficientComplexIsoULift (M : RightLieModuleCat.{w} R L) :
    rightCoefficientComplexULift.{u,v,w,z} R L M ≅
      coefficientComplexULift.{u,v,w,z} R L (RightLieModuleCat.toLeft M) :=
  ((ModuleCat.uliftFunctor.{z, max u v w} R).mapHomologicalComplex
    (ComplexShape.down ℕ)).mapIso (rightCoefficientComplexIso R L M)

theorem rightCoefficientComplexIsoULift_hom_f_tmul
    (M : RightLieModuleCat.{w} R L) (n : ℕ) (m : M) (a : ⋀[R]^n L) :
    ((rightCoefficientComplexIsoULift.{u,v,w,z} R L M).hom.f n).hom
        (ULift.up (m ⊗ₜ[R] a)) = ULift.up (a ⊗ₜ[R] m) := by
  change ULift.up (((rightCoefficientComplexIso R L M).hom.f n).hom (m ⊗ₜ[R] a)) = _
  exact congrArg
    (fun p : (⋀[R]^n L) ⊗[R] RightLieModuleCat.toLeft M => ULift.up.{z, max u v w} p)
    (rightCoefficientComplexIso_hom_f_tmul R L M n m a)

theorem rightCoefficientComplexIsoULift_inv_f_tmul
    (M : RightLieModuleCat.{w} R L) (n : ℕ) (a : ⋀[R]^n L) (m : M) :
    ((rightCoefficientComplexIsoULift.{u,v,w,z} R L M).inv.f n).hom
        (ULift.up (a ⊗ₜ[R] m)) = ULift.up (m ⊗ₜ[R] a) := by
  change ULift.up (((rightCoefficientComplexIso R L M).inv.f n).hom (a ⊗ₜ[R] m)) = _
  exact congrArg (fun p : M ⊗[R] (⋀[R]^n L) => ULift.up.{z, max u v w} p)
    (rightCoefficientComplexIso_inv_f_tmul R L M n a m)

section IndependentLieMaps

variable {L' : Type v'} [LieRing L'] [LieAlgebra R L']
variable (f : L →ₗ⁅R⁆ L')
variable (M : RightLieModuleCat.{w} R L) (N : RightLieModuleCat.{w'} R L')

/-- The joint Lie/coefficient map in a common height, with all universes retained. -/
def rightCoefficientLieComplexMapULift (g : RightLieModuleCat.HomOver f M N) :
    rightCoefficientComplexULift.{u,v,w,max u v v' w w'} R L M ⟶
      rightCoefficientComplexULift.{u,v',w',max u v v' w w'} R L' N :=
  (rightCoefficientComplexIsoULift.{u,v,w,max u v v' w w'} R L M).hom ≫
    coefficientLieComplexMapULift R L f (RightLieModuleCat.toLeft M)
      (RightLieModuleCat.toLeft N) (rightCoefficientLieMapToLeft R L f M N g) ≫
        (rightCoefficientComplexIsoULift.{u,v',w',max u v v' w w'} R L' N).inv

/-- The independent-universe map keeps the right coefficient and ordered exterior values. -/
theorem rightCoefficientLieComplexMapULift_f_tmul
    (g : RightLieModuleCat.HomOver f M N) (n : ℕ) (m : M) (a : ⋀[R]^n L) :
    ((rightCoefficientLieComplexMapULift R L f M N g).f n).hom
        (ULift.up (m ⊗ₜ[R] a)) =
      ULift.up (g.toLinearMap m ⊗ₜ[R] exteriorPower.map n f.toLinearMap a) := by
  let eM := rightCoefficientComplexIsoULift.{u,v,w,max u v v' w w'} R L M
  let eN := rightCoefficientComplexIsoULift.{u,v',w',max u v v' w w'} R L' N
  let gLeft := rightCoefficientLieMapToLeft R L f M N g
  let c := coefficientLieComplexMapULift R L f
    (RightLieModuleCat.toLeft M) (RightLieModuleCat.toLeft N) gLeft
  let uMap :
      (rightCoefficientComplexULift.{u,v,w,max u v v' w w'} R L M).X n ⟶
        (coefficientComplexULift.{u,v,w,max u v v' w w'} R L (RightLieModuleCat.toLeft M)).X n :=
    eM.hom.f n
  let cMap :
      (coefficientComplexULift.{u,v,w,max u v v' w w'} R L (RightLieModuleCat.toLeft M)).X n ⟶
        (coefficientComplexULift.{u,v',w',max u v v' w w'} R L' (RightLieModuleCat.toLeft N)).X n :=
    c.f n
  let vMap :
      (coefficientComplexULift.{u,v',w',max u v v' w w'} R L' (RightLieModuleCat.toLeft N)).X n ⟶
        (rightCoefficientComplexULift.{u,v',w',max u v v' w w'} R L' N).X n :=
    eN.inv.f n
  let p : (rightCoefficientComplexULift.{u,v,w,max u v v' w w'} R L M).X n := ULift.up (m ⊗ₜ[R] a)
  change (uMap ≫ cMap ≫ vMap).hom p = _
  have hComp : (uMap ≫ cMap ≫ vMap).hom p = vMap.hom (cMap.hom (uMap.hom p)) :=
    (ModuleCat.comp_apply uMap (cMap ≫ vMap) p).trans
      (ModuleCat.comp_apply cMap vMap (uMap.hom p))
  have hM : uMap.hom p = ULift.up (a ⊗ₜ[R] m) :=
    rightCoefficientComplexIsoULift_hom_f_tmul R L M n m a
  have hC : cMap.hom (ULift.up (a ⊗ₜ[R] m)) =
      ULift.up (exteriorPower.map n f.toLinearMap a ⊗ₜ[R] (g.toLinearMap m : RightLieModuleCat.toLeft N)) :=
    (coefficientLieComplexMapULift_f_tmul R L f
      (RightLieModuleCat.toLeft M) (RightLieModuleCat.toLeft N) gLeft n a m).trans
      (congrArg (fun y : RightLieModuleCat.toLeft N =>
        ULift.up (exteriorPower.map n f.toLinearMap a ⊗ₜ[R] y))
        (rightCoefficientLieMapToLeft_apply R L f M N g m))
  have hN : vMap.hom
      (ULift.up (exteriorPower.map n f.toLinearMap a ⊗ₜ[R] (g.toLinearMap m : RightLieModuleCat.toLeft N))) =
      ULift.up (g.toLinearMap m ⊗ₜ[R] exteriorPower.map n f.toLinearMap a) :=
    rightCoefficientComplexIsoULift_inv_f_tmul R L' N n
      (exteriorPower.map n f.toLinearMap a) (g.toLinearMap m)
  exact hComp.trans ((congrArg (fun x => vMap.hom (cMap.hom x)) hM).trans
    ((congrArg vMap.hom hC).trans hN))

end IndependentLieMaps

/-- The coefficient-first CE construction is a functor on right coefficients. -/
def rightCoefficientComplexFunctor :
    RightLieModuleCat.{w} R L ⥤ ChainComplex (ModuleCat.{max u v w} R) ℕ := by
  let K : RightLieModuleCat.{w} R L ⥤ ChainComplex (ModuleCat.{max u v w} R) ℕ :=
    RightLieModuleCat.toLeftFunctor (R := R) (L := L) ⋙ coefficientComplexFunctor R L
  let e (M : RightLieModuleCat.{w} R L) : rightCoefficientComplex R L M ≅ K.obj M :=
    rightCoefficientComplexIso R L M
  exact
    { obj := fun M => rightCoefficientComplex R L M
      map := fun {M N} g => (e M).hom ≫ K.map g ≫ (e N).inv
      map_id := by
        intro M
        rw [K.map_id]
        simp only [Category.id_comp, Iso.hom_inv_id]
      map_comp := by
        intro M N P g h
        rw [K.map_comp]
        simp only [Category.assoc, Iso.inv_hom_id_assoc] }

/-- Coefficient functor components are the coefficient map tensored with the identity. -/
theorem rightCoefficientComplexFunctor_map_f_tmul
    {M N : RightLieModuleCat.{w} R L} (g : M ⟶ N) (n : ℕ) (m : M) (a : ⋀[R]^n L) :
    (((rightCoefficientComplexFunctor R L).map g).f n).hom (m ⊗ₜ[R] a) =
      g.toLinearMap m ⊗ₜ[R] a := by
  change (rightCoefficientDegreeEquiv R L N n).symm
    ((((coefficientComplexFunctor R L).map (RightLieModuleCat.toLeftMap g)).f n).hom
      (rightCoefficientDegreeEquiv R L M n (m ⊗ₜ[R] a))) = _
  let F := (((coefficientComplexFunctor R L).map (RightLieModuleCat.toLeftMap g)).f n).hom
  let e := rightCoefficientDegreeEquiv R L N n
  have hM : rightCoefficientDegreeEquiv R L M n (m ⊗ₜ[R] a) = a ⊗ₜ[R] m :=
    TensorProduct.comm_tmul R M.carrier (⋀[R]^n L) m a
  have hPoint : F (a ⊗ₜ[R] m) = a ⊗ₜ[R] (g.toLinearMap m : RightLieModuleCat.toLeft N) :=
    (coefficientComplexFunctor_map_f_tmul (R := R) (L := L)
      (RightLieModuleCat.toLeftMap g) n a m).trans
      (congrArg (fun y : RightLieModuleCat.toLeft N => a ⊗ₜ[R] y)
        (RightLieModuleCat.toLeftMap_apply g m))
  exact (congrArg e.symm ((congrArg F hM).trans hPoint)).trans
    (TensorProduct.comm_symm_tmul R N.carrier (⋀[R]^n L) (g.toLinearMap m) a)

/-- The right coefficient functor is naturally the tensor-reordered left functor. -/
def rightCoefficientComplexFunctorIso :
    rightCoefficientComplexFunctor R L ≅
      RightLieModuleCat.toLeftFunctor (R := R) (L := L) ⋙ coefficientComplexFunctor R L :=
  NatIso.ofComponents (rightCoefficientComplexIso R L) (by
    intro M N g
    let K : RightLieModuleCat.{w} R L ⥤ ChainComplex (ModuleCat.{max u v w} R) ℕ :=
      RightLieModuleCat.toLeftFunctor (R := R) (L := L) ⋙ coefficientComplexFunctor R L
    let eM : rightCoefficientComplex R L M ≅ K.obj M := rightCoefficientComplexIso R L M
    let eN : rightCoefficientComplex R L N ≅ K.obj N := rightCoefficientComplexIso R L N
    change (eM.hom ≫ K.map g ≫ eN.inv) ≫ eN.hom = eM.hom ≫ K.map g
    have hCancel : (K.map g ≫ eN.inv) ≫ eN.hom = K.map g :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun t => K.map g ≫ t) eN.inv_hom_id).trans (Category.comp_id _))
    exact (Category.assoc eM.hom (K.map g ≫ eN.inv) eN.hom).trans
      (congrArg (fun t => eM.hom ≫ t) hCancel))

section Trivial

variable (M : Type w) [AddCommGroup M] [Module R M]

/-- Trivial right coefficients retain exactly the canonical bracket differential. -/
theorem rightCoefficientDifferential_trivial (n : ℕ) :
    rightCoefficientDifferential R L (RightLieModuleCat.trivial (R := R) (L := L) M) n =
      (differential R L n).lTensor M := by
  let T := RightLieModuleCat.trivial (R := R) (L := L) M
  let : LieModule.IsTrivial L (RightLieModuleCat.toLeft T) :=
    ⟨fun x m => by
      rw [RightLieModuleCat.toLeft_lie]
      have h₀ : T.action x m = 0 :=
        RightLieModuleCat.trivial_action (R := R) (L := L) M x m
      exact (congrArg Neg.neg h₀).trans neg_zero⟩
  have h := coefficientDifferential_eq_bracket_of_isTrivial
    R L (RightLieModuleCat.toLeft T) n
  apply TensorProduct.ext'
  intro m a
  change (rightCoefficientDegreeEquiv R L T n).symm
      (coefficientDifferential R L (RightLieModuleCat.toLeft T) n (a ⊗ₜ[R] m)) =
    m ⊗ₜ[R] differential R L n a
  rw [h, LinearMap.rTensor_tmul]
  exact TensorProduct.comm_symm_tmul R T.carrier (⋀[R]^n L) m (differential R L n a)

end Trivial

/-- Trivial scalar coefficients recover the canonical exterior-power CE chain complex. -/
def rightCoefficientTrivialScalarIso :
    rightCoefficientComplex R L (RightLieModuleCat.trivial (R := R) (L := L) R) ≅
      (canonicalChainData R L).complex := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (TensorProduct.lid R (⋀[R]^n L)).toModuleIso) ?_
  intro i j hij
  change j + 1 = i at hij
  subst i
  rw [rightCoefficientComplex_d_succ, ChainData.complex_d_succ]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext' (R := R)
  intro r a
  let r₀ : R := r
  change differential R L j
      (TensorProduct.lid R (⋀[R]^(j + 1) L) (r₀ ⊗ₜ[R] a)) =
    TensorProduct.lid R (⋀[R]^j L)
      (rightCoefficientDifferential R L
        (RightLieModuleCat.trivial (R := R) (L := L) R) j (r₀ ⊗ₜ[R] a))
  have h₀ : rightCoefficientDifferential R L
      (RightLieModuleCat.trivial (R := R) (L := L) R) j (r₀ ⊗ₜ[R] a) =
        (differential R L j).lTensor R (r₀ ⊗ₜ[R] a) :=
    LinearMap.congr_fun (rightCoefficientDifferential_trivial R L R j) (r₀ ⊗ₜ[R] a)
  have hTensor : (differential R L j).lTensor R (r₀ ⊗ₜ[R] a) =
      r₀ ⊗ₜ[R] differential R L j a := by
    simp only [LinearMap.lTensor_tmul]
  have hValue := h₀.trans hTensor
  have hLid : TensorProduct.lid R (⋀[R]^j L) (r₀ ⊗ₜ[R] differential R L j a) =
      r₀ • differential R L j a := by
    simp only [TensorProduct.lid_tmul]
  have hRight := (congrArg (TensorProduct.lid R (⋀[R]^j L)) hValue).trans hLid
  have hLidSource : TensorProduct.lid R (⋀[R]^(j + 1) L) (r₀ ⊗ₜ[R] a) = r₀ • a := by
    simp only [TensorProduct.lid_tmul]
  have hLeft : differential R L j
      (TensorProduct.lid R (⋀[R]^(j + 1) L) (r₀ ⊗ₜ[R] a)) =
        r₀ • differential R L j a :=
    (congrArg (differential R L j) hLidSource).trans ((differential R L j).map_smul r₀ a)
  exact hLeft.trans hRight.symm

end ChevalleyEilenberg
