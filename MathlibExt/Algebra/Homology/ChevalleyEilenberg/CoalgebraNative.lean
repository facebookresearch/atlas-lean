/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.Coalgebra
public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.Canonical
public import MathlibExt.LinearAlgebra.ExteriorAlgebra.CoalgebraGraded
public import MathlibExt.Algebra.Homology.TensorDifferentialDownNat
public import MathlibExt.Algebra.Homology.GradedTensorTower
public import MathlibExt.Algebra.Homology.TensorUnitor
public import MathlibExt.Algebra.Category.ModuleCat.Monoidal.UniverseUnitor
public import MathlibExt.Algebra.Homology.KoszulTensorBraiding
public import MathlibExt.Algebra.Homology.TotalComplexSymmetryDownNat
import Lean.Elab.Tactic.Omega

/-!
# The cocommutative exterior chain coalgebra

Let R:Type u be a commutative ring and L:Type v an R-Lie algebra.
The primitive exterior coproduct gives a chain map
Γ:C_*(L)→C_*(L)⊗C_*(L). In degree n its target is the finite
direct sum of Λ_R^pL⊗Λ_R^qL over p+q=n, and its realization in
E⊗_R E is the exterior coproduct.

The counit has the scalar augmentation in degree zero and vanishes
in positive degrees. The coaugmentation inserts scalars into degree
zero. The tensor unit is ULift.{v}R concentrated in degree zero,
and the chain category is ModuleCat over R at max{u,v}.

These maps satisfy the comonoid and coaugmentation laws.
Cocommutativity uses the Koszul braiding, which sends a degree-(p,q)
tensor a⊗b to (−1)^{pq}b⊗a. The scalar and Lie-carrier universes
are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u v

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R]
variable (L : Type v) [LieRing L] [LieAlgebra R L]

local notation "E" => ExteriorAlgebra R L
local notation "𝓔" => ExteriorAlgebra.gradedExterior R L

open scoped ModuleCat.UniverseTensor

local instance : HasFiniteBiproducts (ModuleCat.{max u v} R) :=
  CategoryTheory.Abelian.hasFiniteBiproducts (C := ModuleCat.{max u v} R)

/-- For a commutative ring R:Type u and any universe v, tensoring
in ModuleCat.{max u v}R has the R-linear Hom module as right
adjoint. This is the closed module tensor structure. -/
local instance nativeCoalgebraClosed : MonoidalClosed (ModuleCat.{max u v} R) :=
  ModuleCat.UniverseScalarRestriction.monoidalClosed.{u,v} (R := R)

/-- Let R:Type u be commutative and L:Type v an R-Lie algebra.
Write C_n=Λ_R^nL for its canonical CE chain complex, E for its
exterior algebra and D=∂⊗id+γ⊗∂ for the signed tensor boundary.
The tensor-square complex C⊗C has degree-n object
⊕_{p+q=n} Λ_R^pL⊗Λ_R^qL and the signed tensor differential. -/
def nativeTensorComplex : ChainComplex (ModuleCat.{max u v} R) ℕ := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  exact HomologicalComplex.tensorObj ((canonicalChainData R L).complex) ((canonicalChainData R L).complex)

@[simp]
theorem nativeTensorComplex_X (n : ℕ) :
    (nativeTensorComplex R L).X n = ExteriorAlgebra.tensorDegree R L n := rfl

private theorem boundary_exterior_zero (a : ⋀[R]^0 L) : boundary R L (a : E) = 0 := by
  have ha : (a : E) ∈ (1 : Submodule R E) := by simpa only [pow_zero] using a.property
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp ha
  rw [← hr]
  exact boundary_algebraMap R L r

private theorem canonicalTensorι_realize_value (p q n : ℕ) (h : p + q = n)
    (a : ⋀[R]^p L) (b : ⋀[R]^q L) :
    (ExteriorAlgebra.tensorDegreeRealize R L n).hom
      ((HomologicalComplex.ιTensorObj ((canonicalChainData R L).complex)
        ((canonicalChainData R L).complex) p q n h).hom (a ⊗ₜ[R] b)) =
    (a : E) ⊗ₜ[R] (b : E) := by
  have hι := congrArg (fun f => f.hom (a ⊗ₜ[R] b))
    (ExteriorAlgebra.tensorDegreeι_realize R L p q n h)
  exact hι

private theorem canonicalComplex_d_hom (n : ℕ) :
    (((canonicalChainData R L).complex).d (n + 1) n).hom = differential R L n := by
  rw [ChainData.complex_d_succ]
  rfl

private theorem addScaled_comp {C : Type*} [Category C] [Preadditive C]
    {A B D : C} (f g : A ⟶ B) (h : B ⟶ D) (z : ℤ) :
    (f + z • g) ≫ h = f ≫ h + z • (g ≫ h) := by
  rw [Preadditive.add_comp, Preadditive.zsmul_comp]

private theorem positiveTensorBoundary_realization (p q : ℕ) :
                ((((canonicalChainData R L).complex).d (p + 1) p) ⊗ₘ
                  𝟙 (((canonicalChainData R L).complex).X (q + 1))) ≫
                  ModuleCat.ofHom (TensorProduct.map (⋀[R]^p L).subtype (⋀[R]^(q + 1) L).subtype) +
                ((-1 : ℤ) ^ (p + 1)) •
                  ((𝟙 (((canonicalChainData R L).complex).X (p + 1)) ⊗ₘ
                    (((canonicalChainData R L).complex).d (q + 1) q)) ≫
                    ModuleCat.ofHom (TensorProduct.map (⋀[R]^(p + 1) L).subtype (⋀[R]^q L).subtype)) =
                ModuleCat.ofHom (TensorProduct.map (⋀[R]^(p + 1) L).subtype
                  (⋀[R]^(q + 1) L).subtype) ≫ ModuleCat.ofHom (tensorBoundary R L) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v}
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v}

  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro (a : ⋀[R]^(p + 1) L) (b : ⋀[R]^(q + 1) L)
  have hValue :
      (differential R L p a : E) ⊗ₜ[R] (b : E) +
        ((-1 : ℤ) ^ (p + 1)) • ((a : E) ⊗ₜ[R] (differential R L q b : E)) =
      tensorBoundary R L ((a : E) ⊗ₜ[R] (b : E)) := by
    have hγ := ExteriorAlgebra.involute_of_mem_exteriorPower
      (A := R) (M := L) (n := p + 1) (x := (a : E)) a.property
    have hsign (t : E ⊗[R] E) :
        ((-1 : ℤ) ^ (p + 1)) • t = (-1 : R) ^ (p + 1) • t := by
      rw [← Int.cast_smul_eq_zsmul R]
      simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]
    rw [tensorBoundary_tmul, differential_coe, differential_coe, hγ, hsign,
      TensorProduct.smul_tmul']
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_zsmul,
    LinearMap.smul_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.UniverseTensor.hom_tensorHom, canonicalComplex_d_hom,
    ModuleCat.hom_id]
  change
    TensorProduct.map (⋀[R]^p L).subtype (⋀[R]^(q + 1) L).subtype
      (TensorProduct.map (differential R L p) LinearMap.id (a ⊗ₜ[R] b)) +
    ((-1 : ℤ) ^ (p + 1)) •
      TensorProduct.map (⋀[R]^(p + 1) L).subtype (⋀[R]^q L).subtype
        (TensorProduct.map LinearMap.id (differential R L q) (a ⊗ₜ[R] b)) =
    tensorBoundary R L
      (TensorProduct.map (⋀[R]^(p + 1) L).subtype (⋀[R]^(q + 1) L).subtype (a ⊗ₜ[R] b))
  simpa only [TensorProduct.map_tmul, LinearMap.id_apply, Submodule.subtype_apply] using hValue

/-- Let R:Type u be commutative and L:Type v an R-Lie algebra.
Write C_n=Λ_R^nL for its canonical CE chain complex, E for its
exterior algebra and D=∂⊗id+γ⊗∂ for the signed tensor boundary.
Let ρ_n:(C⊗C)_n→E⊗_R E realize the homogeneous tensor
summands. It intertwines the chain and ambient differentials:
ρ_n d^{C⊗C}_{n+1}=D ρ_{n+1}. -/
theorem nativeTensorDifferential_realize (n : ℕ) :
    (nativeTensorComplex R L).d (n + 1) n ≫ ExteriorAlgebra.tensorDegreeRealize R L n =
      ExteriorAlgebra.tensorDegreeRealize R L (n + 1) ≫ ModuleCat.ofHom (tensorBoundary R L) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  apply ExteriorAlgebra.tensorDegree_hom_ext R L (n + 1)
  intro p q hpq
  change HomologicalComplex.ιTensorObj ((canonicalChainData R L).complex) ((canonicalChainData R L).complex) p q (n +
    1) hpq ≫
      ((HomologicalComplex.tensorObj ((canonicalChainData R L).complex) ((canonicalChainData R L).complex)).d (n + 1)
        n ≫
        ExteriorAlgebra.tensorDegreeRealize R L n) =
    ExteriorAlgebra.tensorDegreeι R L p q (n + 1) hpq ≫
      (ExteriorAlgebra.tensorDegreeRealize R L (n + 1) ≫ ModuleCat.ofHom (tensorBoundary R L))
  have hD := HomologicalComplex.ιTensorObj_comp_d_down_nat
    ((canonicalChainData R L).complex) ((canonicalChainData R L).complex) p q n hpq
  have hD' := congrArg (fun x => x ≫ ExteriorAlgebra.tensorDegreeRealize R L n) hD
  rw [← Category.assoc]
  exact hD'.trans (by
    have hReal := ExteriorAlgebra.tensorDegreeι_realize R L p q (n + 1) hpq
    have hReal' := congrArg (fun x => x ≫ ModuleCat.ofHom (tensorBoundary R L)) hReal
    rw [hReal']
    cases p with
    | zero =>
        cases q with
        | zero => exact False.elim (Nat.succ_ne_zero n hpq.symm)
        | succ q =>
            have hq : q = n := by omega
            subst q
            simp only [dif_pos rfl, dite_true, dif_neg (Nat.succ_ne_zero n), zero_comp,
              zero_add, Nat.succ_sub_one, pow_zero, one_smul, Category.assoc,
              ExteriorAlgebra.tensorDegreeι_realize]
            have hReal := ExteriorAlgebra.tensorDegreeι_realize R L 0 n n (zero_add n)
            have hd : (((canonicalChainData R L).complex).d (n + 1) n).hom = differential R L n := by
              rw [ChainData.complex_d_succ]
              rfl
            have hι : HomologicalComplex.ιTensorObj ((canonicalChainData R L).complex)
                ((canonicalChainData R L).complex) 0 n n (zero_add n) ≫
                ExteriorAlgebra.tensorDegreeRealize R L n =
              ModuleCat.ofHom (TensorProduct.map (⋀[R]^0 L).subtype (⋀[R]^n L).subtype) :=
              ExteriorAlgebra.tensorDegreeι_realize R L 0 n n (zero_add n)
            have hι' := congrArg (fun y =>
              (𝟙 (((canonicalChainData R L).complex).X 0) ⊗ₘ
                (((canonicalChainData R L).complex).d (n + 1) n)) ≫ y) hι
            exact (Category.assoc _ _ _).trans (hι'.trans (by
              apply ModuleCat.hom_ext
              apply TensorProduct.ext'
              intro (a : ⋀[R]^0 L) (b : ⋀[R]^(n + 1) L)
              simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
                ModuleCat.UniverseTensor.hom_tensorHom, TensorProduct.map_tmul,
                ModuleCat.hom_id, LinearMap.id_apply, canonicalComplex_d_hom]
              have hγ : CliffordAlgebra.involute (a : E) = (a : E) := by
                simpa only [pow_zero, one_smul] using
                  ExteriorAlgebra.involute_of_mem_exteriorPower
                    (A := R) (M := L) (n := 0) (x := (a : E)) a.property
              change (a : E) ⊗ₜ[R] (differential R L n b : E) =
                tensorBoundary R L ((a : E) ⊗ₜ[R] (b : E))
              rw [tensorBoundary_tmul, boundary_exterior_zero R L a, hγ,
                TensorProduct.zero_tmul, zero_add, differential_coe]))
    | succ p =>
        cases q with
        | zero =>
            have hp : p = n := by omega
            subst p
            simp only [dif_pos rfl, dite_true, dif_neg (Nat.succ_ne_zero n), zero_comp,
              add_zero, Nat.succ_sub_one, Category.assoc, ExteriorAlgebra.tensorDegreeι_realize]
            have hι : HomologicalComplex.ιTensorObj ((canonicalChainData R L).complex)
                ((canonicalChainData R L).complex) n 0 n (add_zero n) ≫
                ExteriorAlgebra.tensorDegreeRealize R L n =
              ModuleCat.ofHom (TensorProduct.map (⋀[R]^n L).subtype (⋀[R]^0 L).subtype) :=
              ExteriorAlgebra.tensorDegreeι_realize R L n 0 n (add_zero n)
            have hι' := congrArg (fun y =>
              ((((canonicalChainData R L).complex).d (n + 1) n) ⊗ₘ
                𝟙 (((canonicalChainData R L).complex).X 0)) ≫ y) hι
            exact (Category.assoc _ _ _).trans (hι'.trans (by
              apply ModuleCat.hom_ext
              apply TensorProduct.ext'
              intro (a : ⋀[R]^(n + 1) L) (b : ⋀[R]^0 L)
              simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
                ModuleCat.UniverseTensor.hom_tensorHom, TensorProduct.map_tmul,
                ModuleCat.hom_id, LinearMap.id_apply, canonicalComplex_d_hom]
              change (differential R L n a : E) ⊗ₜ[R] (b : E) =
                tensorBoundary R L ((a : E) ⊗ₜ[R] (b : E))
              rw [tensorBoundary_tmul, boundary_exterior_zero R L b,
                TensorProduct.tmul_zero, add_zero, differential_coe]))
        | succ q =>
            have hn : n = p + q + 1 := by omega
            subst n
            simp only [dif_neg (Nat.succ_ne_zero p), dif_neg (Nat.succ_ne_zero q),
              Nat.succ_sub_one, Category.assoc, ExteriorAlgebra.tensorDegreeι_realize,
              Preadditive.add_comp, Preadditive.zsmul_comp]
            have h₁ := ExteriorAlgebra.tensorDegreeι_realize R L p (q + 1)
              (p + q + 1) (by omega)
            have h₂ := ExteriorAlgebra.tensorDegreeι_realize R L (p + 1) q
              (p + q + 1) (by omega)
            have h₁' := congrArg (fun x =>
              ((((canonicalChainData R L).complex).d (p + 1) p) ⊗ₘ
                𝟙 (((canonicalChainData R L).complex).X (q + 1))) ≫ x) h₁
            have h₂' := congrArg (fun x =>
              (𝟙 (((canonicalChainData R L).complex).X (p + 1)) ⊗ₘ
                (((canonicalChainData R L).complex).d (q + 1) q)) ≫ x) h₂
            have hSum := congrArg₂ (fun x y => x + ((-1 : ℤ) ^ (p + 1)) • y) h₁' h₂'
            have hSum' := hSum
            have hValue := positiveTensorBoundary_realization R L p q
            simp only [ChainData.complex_X] at hSum
            dsimp only [chainObject] at hSum
            have hAll := hSum.trans (positiveTensorBoundary_realization R L p q)
            have h₁eq : HomologicalComplex.ιTensorObj ((canonicalChainData R L).complex)
                ((canonicalChainData R L).complex) p (q + 1) (p + q + 1) (by omega) =
              ExteriorAlgebra.tensorDegreeι R L p (q + 1) (p + q + 1) (by omega) := rfl
            have h₂eq : HomologicalComplex.ιTensorObj ((canonicalChainData R L).complex)
                ((canonicalChainData R L).complex) (p + 1) q (p + q + 1) (by omega) =
              ExteriorAlgebra.tensorDegreeι R L (p + 1) q (p + q + 1) (by omega) := rfl
            rw [h₁eq, h₂eq]
            have hNorm := addScaled_comp
              (((((canonicalChainData R L).complex).d (p + 1) p) ⊗ₘ
                𝟙 (((canonicalChainData R L).complex).X (q + 1))) ≫
                ExteriorAlgebra.tensorDegreeι R L p (q + 1) (p + q + 1) (by omega))
              ((𝟙 (((canonicalChainData R L).complex).X (p + 1)) ⊗ₘ
                (((canonicalChainData R L).complex).d (q + 1) q)) ≫
                ExteriorAlgebra.tensorDegreeι R L (p + 1) q (p + q + 1) (by omega))
              (ExteriorAlgebra.tensorDegreeRealize R L (p + q + 1)) ((-1 : ℤ) ^ (p + 1))
            simp only [ChainData.complex_X] at hNorm ⊢
            dsimp only [chainObject] at hNorm ⊢
            simp only [ChainData.complex_X] at hAll
            let dp : ModuleCat.of R (⋀[R]^(p + 1) L) ⟶ ModuleCat.of R (⋀[R]^p L) :=
              ((canonicalChainData R L).complex).d (p + 1) p
            let dq : ModuleCat.of R (⋀[R]^(q + 1) L) ⟶ ModuleCat.of R (⋀[R]^q L) :=
              ((canonicalChainData R L).complex).d (q + 1) q
            have hAssoc₁ := Category.assoc
              (dp ⊗ₘ 𝟙 (ModuleCat.of R (⋀[R]^(q + 1) L)))
              (ExteriorAlgebra.tensorDegreeι R L p (q + 1) (p + q + 1) (by omega))
              (ExteriorAlgebra.tensorDegreeRealize R L (p + q + 1))
            have hAssoc₂ := Category.assoc
              (𝟙 (ModuleCat.of R (⋀[R]^(p + 1) L)) ⊗ₘ dq)
              (ExteriorAlgebra.tensorDegreeι R L (p + 1) q (p + q + 1) (by omega))
              (ExteriorAlgebra.tensorDegreeRealize R L (p + q + 1))
            have hAssoc := congrArg₂ (fun x y => x + ((-1 : ℤ) ^ (p + 1)) • y) hAssoc₁ hAssoc₂
            exact hNorm.trans (hAssoc.trans hAll))

/-- Let R:Type u be commutative and L:Type v an R-Lie algebra.
Write C_n=Λ_R^nL for its canonical CE chain complex, E for its
exterior algebra and D=∂⊗id+γ⊗∂ for the signed tensor boundary.
The homogeneous exterior coproduct gives the chain map
Γ:C→C⊗C, with each component the sum of its degree-(p,q)
projections for p+q=n. -/
def nativeComplexComul : ((canonicalChainData R L).complex) ⟶ nativeTensorComplex R L where
  f n := ExteriorAlgebra.gradedCoproduct R L n
  comm' i j h := by
    change j + 1 = i at h
    subst i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply ExteriorAlgebra.tensorDegreeRealize_injective R L j
    have ht := congrArg (fun f => f.hom ((ExteriorAlgebra.gradedCoproduct R L (j + 1)).hom a))
      (nativeTensorDifferential_realize R L j)
    have hi := congrArg (fun f => f.hom a) (ExteriorAlgebra.gradedCoproduct_realize R L (j + 1))
    have hj := congrArg (fun f => f.hom ((((canonicalChainData R L).complex).d (j + 1) j).hom a))
      (ExteriorAlgebra.gradedCoproduct_realize R L j)
    change (ExteriorAlgebra.tensorDegreeRealize R L j).hom
        (((nativeTensorComplex R L).d (j + 1) j).hom
          ((ExteriorAlgebra.gradedCoproduct R L (j + 1)).hom a)) =
      tensorBoundary R L ((ExteriorAlgebra.tensorDegreeRealize R L (j + 1)).hom
        ((ExteriorAlgebra.gradedCoproduct R L (j + 1)).hom a)) at ht
    change (ExteriorAlgebra.tensorDegreeRealize R L (j + 1)).hom
        ((ExteriorAlgebra.gradedCoproduct R L (j + 1)).hom a) =
      ExteriorAlgebra.coproduct R L ((show ⋀[R]^(j + 1) L from a) : E) at hi
    change (ExteriorAlgebra.tensorDegreeRealize R L j).hom
        ((ExteriorAlgebra.gradedCoproduct R L j).hom
          ((((canonicalChainData R L).complex).d (j + 1) j).hom a)) =
      ExteriorAlgebra.coproduct R L
        ((show ⋀[R]^j L from ((((canonicalChainData R L).complex).d (j + 1) j).hom a)) : E) at hj
    change (ExteriorAlgebra.tensorDegreeRealize R L j).hom
        (((nativeTensorComplex R L).d (j + 1) j).hom
          ((ExteriorAlgebra.gradedCoproduct R L (j + 1)).hom a)) =
      (ExteriorAlgebra.tensorDegreeRealize R L j).hom
        ((ExteriorAlgebra.gradedCoproduct R L j).hom
          ((((canonicalChainData R L).complex).d (j + 1) j).hom a))
    have hd : (((canonicalChainData R L).complex).d (j + 1) j).hom = differential R L j := by
      rw [ChainData.complex_d_succ]
      rfl
    have hBoundary : tensorBoundary R L
        (ExteriorAlgebra.coproduct R L ((show ⋀[R]^(j + 1) L from a) : E)) =
      ExteriorAlgebra.coproduct R L
        ((show ⋀[R]^j L from ((((canonicalChainData R L).complex).d (j + 1) j).hom a)) : E) := by
      rw [hd]
      change tensorBoundary R L
          (ExteriorAlgebra.coproduct R L ((show ⋀[R]^(j + 1) L from a) : E)) =
        ExteriorAlgebra.coproduct R L
          ((show ⋀[R]^j L from differential R L j (show ⋀[R]^(j + 1) L from a)) : E)
      rw [differential_coe, coproduct_boundary]
    exact ht.trans ((congrArg (tensorBoundary R L) hi).trans (hBoundary.trans hj.symm))

@[simp]
theorem nativeComplexComul_f (n : ℕ) :
    (nativeComplexComul R L).f n = ExteriorAlgebra.gradedCoproduct R L n := rfl

/-- Let R:Type u be commutative and L:Type v an R-Lie algebra.
Write C_n=Λ_R^nL for its canonical CE chain complex, E for its
exterior algebra and D=∂⊗id+γ⊗∂ for the signed tensor boundary.
The chain tensor unit is ULift.{v}R in degree zero and zero
in every positive degree, in ModuleCat at max{u,v}. -/
def nativeUnitComplex : ChainComplex (ModuleCat.{max u v} R) ℕ := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  exact HomologicalComplex.tensorUnit (ModuleCat.{max u v} R) (ComplexShape.down ℕ)

/-- Let R:Type u be commutative and L:Type v an R-Lie algebra.
Write C_n=Λ_R^nL for its canonical CE chain complex, E for its
exterior algebra and D=∂⊗id+γ⊗∂ for the signed tensor boundary.
The graded unit, concentrated in degree zero at ULift.{v}R,
is isomorphic to the underlying graded objects of the chain tensor unit. -/
def unitGradingIso : (ExteriorAlgebra.gradedUnit.{u,v} R) ≅ (nativeUnitComplex.{u,v} R).X := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  exact HomologicalComplex.tensorUnitIso (ModuleCat.{max u v} R) (ComplexShape.down ℕ)

private theorem nativeUnitComplex_d (i j : ℕ) : (nativeUnitComplex.{u,v} R).d i j = 0 := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  exact HomologicalComplex.single_obj_d _ _ _ _ _

private theorem canonicalComplex_d_one_zero : ((canonicalChainData R L).complex).d 1 0 = 0 := by
  rw [ChainData.complex_d_succ]
  have h := PresentedData.d_zero (canonicalPresentedData R L)
  change ModuleCat.ofHom (differential R L 0) = 0
  rw [show differential R L 0 = 0 from h, ModuleCat.ofHom_zero]

/-- Let R:Type u be commutative and L:Type v an R-Lie algebra.
Write C_n=Λ_R^nL for its canonical CE chain complex, E for its
exterior algebra and D=∂⊗id+γ⊗∂ for the signed tensor boundary.
The exterior augmentation defines the chain counit ε:C→𝟙.
It takes the degree-zero scalar coordinate to ULift.{v}R and
is zero on every positive degree. -/
def nativeComplexCounit : ((canonicalChainData R L).complex) ⟶ nativeUnitComplex.{u,v} R where
  f n := ExteriorAlgebra.gradedCounit R L n ≫ (unitGradingIso.{u,v} R).hom n
  comm' i j h := by
    change j + 1 = i at h
    subst i
    rw [nativeUnitComplex_d, comp_zero]
    by_cases hj : j = 0
    · subst j
      rw [canonicalComplex_d_one_zero, zero_comp]
    · have hz : (ExteriorAlgebra.gradedCounit R L j ≫ (unitGradingIso.{u,v} R).hom j) = 0 := by
        rw [ExteriorAlgebra.gradedCounit_ne R L j hj, zero_comp]
      exact ((congrArg (fun x => (((canonicalChainData R L).complex).d (j + 1) j) ≫ x) hz).trans
        (comp_zero)).symm

/-- Let R:Type u be commutative and L:Type v an R-Lie algebra.
Write C_n=Λ_R^nL for its canonical CE chain complex, E for its
exterior algebra and D=∂⊗id+γ⊗∂ for the signed tensor boundary.
The scalar inclusion defines the chain coaugmentation u:𝟙→C.
In degree zero it sends the lifted scalar r to its exterior scalar,
and it vanishes in positive degrees. -/
def nativeComplexCoaug : nativeUnitComplex.{u,v} R ⟶ ((canonicalChainData R L).complex) where
  f n := (unitGradingIso.{u,v} R).inv n ≫ ExteriorAlgebra.gradedCoaug R L n
  comm' i j h := by
    change j + 1 = i at h
    subst i
    rw [nativeUnitComplex_d, zero_comp]
    have hz : ((unitGradingIso.{u,v} R).inv (j + 1) ≫
        ExteriorAlgebra.gradedCoaug R L (j + 1)) = 0 := by
      rw [ExteriorAlgebra.gradedCoaug_ne R L (j + 1) (Nat.succ_ne_zero j), comp_zero]
    exact (congrArg (fun x => x ≫ (((canonicalChainData R L).complex).d (j + 1) j)) hz).trans
      (zero_comp)

@[simp]
theorem nativeComplexCounit_f (n : ℕ) : (nativeComplexCounit R L).f n =
    ExteriorAlgebra.gradedCounit R L n ≫ (unitGradingIso.{u,v} R).hom n := rfl

@[simp]
theorem nativeComplexCoaug_f (n : ℕ) : (nativeComplexCoaug R L).f n =
    (unitGradingIso.{u,v} R).inv n ≫ ExteriorAlgebra.gradedCoaug R L n := rfl

/-- Let R:Type u be commutative and L:Type v an R-Lie algebra.
Write C_n=Λ_R^nL for its canonical CE chain complex, E for its
exterior algebra and D=∂⊗id+γ⊗∂ for the signed tensor boundary.
The chain coproduct Γ and counit ε satisfy coassociativity
and both counit identities, making C a comonoid in the signed tensor
category of nonnegative R-module complexes. -/
def nativeComonObj :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
    ComonObj ((canonicalChainData R L).complex) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  letI : ComonObj 𝓔 := ExteriorAlgebra.gradedComonObj R L
  exact
    { counit := nativeComplexCounit R L
      comul := nativeComplexComul R L
      counit_comul := by
        apply HomologicalComplex.hom_ext
        intro n
        have hg : ExteriorAlgebra.gradedCoproduct R L ≫
            GradedObject.Monoidal.tensorHom (ExteriorAlgebra.gradedCounit R L) (𝟙 𝓔) =
          (GradedObject.Monoidal.leftUnitor 𝓔).inv := ComonObj.counit_comul 𝓔
        have ht : GradedObject.Monoidal.tensorHom
            (ExteriorAlgebra.gradedCounit R L ≫ (unitGradingIso.{u,v} R).hom) (𝟙 𝓔) =
          GradedObject.Monoidal.tensorHom (ExteriorAlgebra.gradedCounit R L) (𝟙 𝓔) ≫
            GradedObject.Monoidal.tensorHom (unitGradingIso.{u,v} R).hom (𝟙 𝓔) := by
          simpa only [Category.comp_id] using
            (GradedObject.Monoidal.tensorHom_comp_tensorHom
              (ExteriorAlgebra.gradedCounit R L) (unitGradingIso.{u,v} R).hom
              (𝟙 𝓔) (𝟙 𝓔)).symm
        have h := congrFun (show ExteriorAlgebra.gradedCoproduct R L ≫
            GradedObject.Monoidal.tensorHom
              (ExteriorAlgebra.gradedCounit R L ≫ (unitGradingIso.{u,v} R).hom) (𝟙 𝓔) =
          (GradedObject.Monoidal.leftUnitor 𝓔).inv ≫
            GradedObject.Monoidal.tensorHom (unitGradingIso.{u,v} R).hom (𝟙 𝓔) by
          have h₁ := congrArg (fun x => ExteriorAlgebra.gradedCoproduct R L ≫ x) ht
          have h₂ := congrArg (fun x => x ≫
            GradedObject.Monoidal.tensorHom (unitGradingIso.{u,v} R).hom (𝟙 𝓔)) hg
          exact h₁.trans ((Category.assoc _ _ _).symm.trans h₂)) n
        change _ = (HomologicalComplex.leftUnitor' ((canonicalChainData R L).complex)).inv n
        exact h
      comul_counit := by
        apply HomologicalComplex.hom_ext
        intro n
        have hg : ExteriorAlgebra.gradedCoproduct R L ≫
            GradedObject.Monoidal.tensorHom (𝟙 𝓔) (ExteriorAlgebra.gradedCounit R L) =
          (GradedObject.Monoidal.rightUnitor 𝓔).inv := ComonObj.comul_counit 𝓔
        have ht : GradedObject.Monoidal.tensorHom (𝟙 𝓔)
            (ExteriorAlgebra.gradedCounit R L ≫ (unitGradingIso.{u,v} R).hom) =
          GradedObject.Monoidal.tensorHom (𝟙 𝓔) (ExteriorAlgebra.gradedCounit R L) ≫
            GradedObject.Monoidal.tensorHom (𝟙 𝓔) (unitGradingIso.{u,v} R).hom := by
          simpa only [Category.comp_id] using
            (GradedObject.Monoidal.tensorHom_comp_tensorHom (𝟙 𝓔) (𝟙 𝓔)
              (ExteriorAlgebra.gradedCounit R L) (unitGradingIso.{u,v} R).hom).symm
        have h := congrFun (show ExteriorAlgebra.gradedCoproduct R L ≫
            GradedObject.Monoidal.tensorHom (𝟙 𝓔)
              (ExteriorAlgebra.gradedCounit R L ≫ (unitGradingIso.{u,v} R).hom) =
          (GradedObject.Monoidal.rightUnitor 𝓔).inv ≫
            GradedObject.Monoidal.tensorHom (𝟙 𝓔) (unitGradingIso.{u,v} R).hom by
          have h₁ := congrArg (fun x => ExteriorAlgebra.gradedCoproduct R L ≫ x) ht
          have h₂ := congrArg (fun x => x ≫
            GradedObject.Monoidal.tensorHom (𝟙 𝓔) (unitGradingIso.{u,v} R).hom) hg
          exact h₁.trans ((Category.assoc _ _ _).symm.trans h₂)) n
        change _ = (HomologicalComplex.rightUnitor' ((canonicalChainData R L).complex)).inv n
        exact h
      comul_assoc := by
        apply HomologicalComplex.hom_ext
        intro n
        exact ExteriorAlgebra.gradedCoproduct_coassoc R L n }

/-- Let R:Type u be commutative and L:Type v an R-Lie algebra.
Write C_n=Λ_R^nL for its canonical CE chain complex, E for its
exterior algebra and D=∂⊗id+γ⊗∂ for the signed tensor boundary.
The coaugmentation u:𝟙→C and counit ε satisfy εu=id_𝟙. -/
theorem nativeComplexCoaug_counit :
    nativeComplexCoaug R L ≫ nativeComplexCounit R L = 𝟙 (nativeUnitComplex.{u,v} R) := by
  apply HomologicalComplex.hom_ext
  intro n
  have hg := congrFun (ExteriorAlgebra.gradedCoaug_counit R L) n
  change ExteriorAlgebra.gradedCoaug R L n ≫ ExteriorAlgebra.gradedCounit R L n =
    𝟙 ((ExteriorAlgebra.gradedUnit.{u,v} R) n) at hg
  change ((unitGradingIso.{u,v} R).inv n ≫ ExteriorAlgebra.gradedCoaug R L n) ≫
      (ExteriorAlgebra.gradedCounit R L n ≫ (unitGradingIso.{u,v} R).hom n) = 𝟙 _
  rw [Category.assoc, ← Category.assoc (ExteriorAlgebra.gradedCoaug R L n), hg]
  simp only [Category.id_comp]
  exact congrFun (unitGradingIso.{u,v} R).inv_hom_id n

private theorem unitGradingIso_zero_inv : (unitGradingIso.{u,v} R).inv 0 =
    (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
      (ModuleCat.of R (ULift.{v} R))).hom ≫ (ExteriorAlgebra.gradedUnitZeroIso.{u,v} R).inv := rfl

theorem nativeComplexCoaug_zero_value (r : (nativeUnitComplex.{u,v} R).X 0) :
    ((show ⋀[R]^0 L from ((nativeComplexCoaug R L).f 0).hom r) : E) =
      ((HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
        (ModuleCat.of R (ULift.{v} R))).hom.hom r).down • (1 : E) := by
  change ((show ⋀[R]^0 L from (ExteriorAlgebra.gradedCoaug R L 0).hom
    ((unitGradingIso.{u,v} R).inv 0 r)) : E) = _
  rw [ExteriorAlgebra.gradedCoaug_zero_value, unitGradingIso_zero_inv]
  have hr := congrArg (fun f => f.hom
      ((HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
        (ModuleCat.of R (ULift.{v} R))).hom.hom r))
    (ExteriorAlgebra.gradedUnitZeroIso.{u,v} R).inv_hom_id
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
    LinearMap.id_apply] at hr
  exact congrArg (fun x : ULift.{v} R => x.down • (1 : E)) hr

private theorem nativeCoaug_zero_one :
    ((show ⋀[R]^0 L from ((nativeComplexCoaug R L).f 0).hom
      ((HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
        (ModuleCat.of R (ULift.{v} R))).inv.hom (ULift.up (1 : R)))) : E) = 1 := by
  have hv := nativeComplexCoaug_zero_value R L
    ((HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
      (ModuleCat.of R (ULift.{v} R))).inv.hom (ULift.up (1 : R)))
  have hi := congrArg (fun f => f.hom (ULift.up (1 : R)))
    (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
      (ModuleCat.of R (ULift.{v} R))).inv_hom_id
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
    LinearMap.id_apply] at hi
  exact hv.trans ((congrArg (fun x : ULift.{v} R => x.down • (1 : E)) hi).trans
    (one_smul R (1 : E)))

private theorem nativeUnit_leftUnitor_inv_zero (r : (nativeUnitComplex.{u,v} R).X 0) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
    ((HomologicalComplex.leftUnitor (nativeUnitComplex.{u,v} R)).inv.f 0).hom r =
      (HomologicalComplex.ιTensorObj (nativeUnitComplex.{u,v} R) (nativeUnitComplex.{u,v} R)
        0 0 0 rfl).hom
        (((HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
          (ModuleCat.of R (ULift.{v} R))).inv.hom (ULift.up (1 : R))) ⊗ₜ[R] r) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  change ((HomologicalComplex.leftUnitor' (nativeUnitComplex.{u,v} R)).inv 0).hom r = _
  rw [HomologicalComplex.leftUnitor'_inv]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.UniverseTensor.hom_whiskerRight]
  rw [ModuleCat.UniverseTensor.leftUnitor_inv_apply.{u,v} R
    ((nativeUnitComplex.{u,v} R).X 0) r, LinearMap.rTensor_tmul]
  dsimp only [nativeUnitComplex, HomologicalComplex.tensorUnit] at r ⊢
  rfl

/-- Let R:Type u be commutative and L:Type v an R-Lie algebra.
Write C_n=Λ_R^nL for its canonical CE chain complex, E for its
exterior algebra and D=∂⊗id+γ⊗∂ for the signed tensor boundary.
The coaugmentation preserves coproducts:
Γu=(u⊗u)Γ_𝟙, where Γ_𝟙 is the tensor-unit coproduct. -/
theorem nativeComplexCoaug_comul :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
    nativeComplexCoaug R L ≫ nativeComplexComul R L =
      (HomologicalComplex.leftUnitor (nativeUnitComplex.{u,v} R)).inv ≫
        HomologicalComplex.tensorHom (nativeComplexCoaug R L) (nativeComplexCoaug R L) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = 0
  · subst n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    apply ExteriorAlgebra.tensorDegreeRealize_injective R L 0
    let r₁ := (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
      (ModuleCat.of R (ULift.{v} R))).inv.hom (ULift.up (1 : R))
    have ht := congrArg (fun f => f.hom (r₁ ⊗ₜ[R] r))
      (HomologicalComplex.ιTensorObj_tensorHom (nativeComplexCoaug R L) (nativeComplexCoaug R L)
        0 0 0 rfl)
    have hr := congrArg (fun f => f.hom
        (((nativeComplexCoaug R L).f 0).hom r₁ ⊗ₜ[R] ((nativeComplexCoaug R L).f 0).hom r))
      (ExteriorAlgebra.tensorDegreeι_realize R L 0 0 0 rfl)
    have hd := congrArg (fun f => f.hom (((nativeComplexCoaug R L).f 0).hom r))
      (ExteriorAlgebra.gradedCoproduct_realize R L 0)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      ModuleCat.UniverseTensor.hom_tensorHom, TensorProduct.map_tmul] at ht hr hd
    change (ExteriorAlgebra.tensorDegreeRealize R L 0).hom
        (((nativeComplexComul R L).f 0).hom (((nativeComplexCoaug R L).f 0).hom r)) =
      (ExteriorAlgebra.tensorDegreeRealize R L 0).hom
        (((HomologicalComplex.tensorHom (nativeComplexCoaug R L) (nativeComplexCoaug R L)).f 0).hom
          (((HomologicalComplex.leftUnitor (nativeUnitComplex.{u,v} R)).inv.f 0).hom r))
    change (ExteriorAlgebra.tensorDegreeRealize R L 0).hom
        ((ExteriorAlgebra.gradedCoproduct R L 0).hom ((nativeComplexCoaug R L).f 0 r)) =
      ExteriorAlgebra.coproduct R L
        ((show ⋀[R]^0 L from (nativeComplexCoaug R L).f 0 r) : E) at hd
    have hD : ((nativeComplexComul R L).f 0).hom
        (((nativeComplexCoaug R L).f 0).hom r) =
      (ExteriorAlgebra.gradedCoproduct R L 0).hom (((nativeComplexCoaug R L).f 0).hom r) := rfl
    have hD' := congrArg (ExteriorAlgebra.tensorDegreeRealize R L 0).hom hD
    rw [hD']
    rw [hd, nativeUnit_leftUnitor_inv_zero.{u,v} R r, ht]
    have hr' := hr
    change (ExteriorAlgebra.tensorDegreeRealize R L 0).hom
      ((HomologicalComplex.ιTensorObj ((canonicalChainData R L).complex)
        ((canonicalChainData R L).complex) 0 0 0 rfl).hom
        (TensorProduct.map ((nativeComplexCoaug R L).f 0).hom ((nativeComplexCoaug R L).f 0).hom
          (r₁ ⊗ₜ[R] r))) =
      ((show ⋀[R]^0 L from (nativeComplexCoaug R L).f 0 r₁) : E) ⊗ₜ[R]
        ((show ⋀[R]^0 L from (nativeComplexCoaug R L).f 0 r) : E) at hr'
    rw [hr']
    change ExteriorAlgebra.coproduct R L ((show ⋀[R]^0 L from ((nativeComplexCoaug R L).f 0).hom r) : E) =
      ((show ⋀[R]^0 L from ((nativeComplexCoaug R L).f 0).hom r₁) : E) ⊗ₜ[R]
        ((show ⋀[R]^0 L from ((nativeComplexCoaug R L).f 0).hom r) : E)
    rw [nativeCoaug_zero_one, nativeComplexCoaug_zero_value, map_smul,
      ExteriorAlgebra.coproduct_one, TensorProduct.tmul_smul]
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
      (ModuleCat.of R (ULift.{v} R)) n hn).eq_of_src _ _

/-- Let R:Type u be commutative and L:Type v an R-Lie algebra.
Write C_n=Λ_R^nL for its canonical CE chain complex, E for its
exterior algebra and D=∂⊗id+γ⊗∂ for the signed tensor boundary.
The coaugmentation u:𝟙→C is a comonoid morphism, preserving
the tensor-unit coproduct and counit. -/
def nativeComplexCoaugIsComonHom :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
    letI : ComonObj ((canonicalChainData R L).complex) := nativeComonObj R L
    letI : ComonObj (nativeUnitComplex.{u,v} R) := ComonObj.instTensorUnit (ChainComplex (ModuleCat.{max u v} R) ℕ)
    IsComonHom (nativeComplexCoaug R L) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  letI : ComonObj ((canonicalChainData R L).complex) := nativeComonObj R L
  letI : ComonObj (nativeUnitComplex.{u,v} R) := ComonObj.instTensorUnit (ChainComplex (ModuleCat.{max u v} R) ℕ)
  exact ⟨nativeComplexCoaug_counit R L, nativeComplexCoaug_comul R L⟩

/-- Let R:Type u be commutative and L:Type v an R-Lie algebra.
Write C_n=Λ_R^nL for its canonical CE chain complex, E for its
exterior algebra and D=∂⊗id+γ⊗∂ for the signed tensor boundary.
The chain coproduct is cocommutative for the Koszul braiding:
τΓ=Γ, where τ(a_p⊗b_q)=(−1)^{pq}b_q⊗a_p. -/
theorem nativeComplexComul_cocommutative :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
    letI : SymmetricCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.symmetricCategory.{u,v} (R := R)
    nativeComplexComul R L ≫ (HomologicalComplex.koszulTensorBraidingIso ((canonicalChainData R L).complex)
      ((canonicalChainData R L).complex)).hom =
      nativeComplexComul R L := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  letI : SymmetricCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.symmetricCategory.{u,v} (R := R)
  apply HomologicalComplex.hom_ext
  intro n
  have hswap : (HomologicalComplex.koszulTensorBraidingIso ((canonicalChainData R L).complex) ((canonicalChainData R
    L).complex)).hom.f n =
      ExteriorAlgebra.gradedKoszulSwap R L n := by
    apply ExteriorAlgebra.tensorDegree_hom_ext R L n
    intro p q h
    change HomologicalComplex.ιTensorObj ((canonicalChainData R L).complex)
      ((canonicalChainData R L).complex) p q n h ≫ _ = _
    have hGraded := ExteriorAlgebra.tensorDegreeι_koszulSwap R L p q n h
    rw [HomologicalComplex.ιTensorObj_koszulTensorBraidingIso_hom]
    have hSign :
        (ComplexShape.down ℕ).σ (ComplexShape.down ℕ) (ComplexShape.down ℕ) p q •
          (β_ (((canonicalChainData R L).complex).X p)
            (((canonicalChainData R L).complex).X q)).hom ≫
          HomologicalComplex.ιTensorObj ((canonicalChainData R L).complex)
            ((canonicalChainData R L).complex) q p n (by omega) =
        (-1 : R) ^ (p * q) •
          (ModuleCat.ofHom (TensorProduct.comm R (⋀[R]^p L) (⋀[R]^q L)).toLinearMap ≫
            ExteriorAlgebra.tensorDegreeι R L q p n (by omega)) := by
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro a b
      change ((-1 : ℤˣ) ^ (p * q)) •
          (ExteriorAlgebra.tensorDegreeι R L q p n (by omega)).hom (b ⊗ₜ[R] a) =
        (-1 : R) ^ (p * q) •
          (ExteriorAlgebra.tensorDegreeι R L q p n (by omega)).hom (b ⊗ₜ[R] a)
      rw [@Units.smul_def _ _ (_) (_), ← Int.cast_smul_eq_zsmul R]
      simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
        Int.cast_pow, Int.cast_neg, Int.cast_one]
    exact hSign.trans hGraded.symm
  change ExteriorAlgebra.gradedCoproduct R L n ≫
      (HomologicalComplex.koszulTensorBraidingIso ((canonicalChainData R L).complex) ((canonicalChainData R
        L).complex)).hom.f n = ExteriorAlgebra.gradedCoproduct R L n
  rw [hswap]
  exact ExteriorAlgebra.gradedCoproduct_cocommutative R L n

/-- Let R:Type u be commutative and L:Type v an R-Lie algebra.
Write C_n=Λ_R^nL for its canonical CE chain complex, E for its
exterior algebra and D=∂⊗id+γ⊗∂ for the signed tensor boundary.
The complex C with its coproduct and counit is the bundled
coalgebra object in ChainComplex(ModuleCat R,ℕ), at height max{u,v}. -/
def nativeCoalgebra :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
    letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
    letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
    letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
    Comon (ChainComplex (ModuleCat.{max u v} R) ℕ) := by
  letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.tensorStructure.{u,v} (R := R)
  letI : MonoidalCategory (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalCategory.{u,v} (R := R)
  letI : MonoidalPreadditive (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalPreadditive.{u,v} (R := R)
  letI : MonoidalLinear R (ModuleCat.{max u v} R) := ModuleCat.UniverseTensor.monoidalLinear.{u,v} (R := R)
  exact { X := (canonicalChainData R L).complex, comon := nativeComonObj R L }

end ChevalleyEilenberg
