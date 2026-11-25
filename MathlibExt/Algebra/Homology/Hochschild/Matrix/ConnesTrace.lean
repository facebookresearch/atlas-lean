/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.Matrix.CyclicTrace
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Cyclic

/-!
# Matrix trace on the Connes quotient

The integral generalized trace preserves the signed
cyclic relations and descends through the first-column
cokernel of the cyclic bicomplex. It retains the
Hochschild boundary and its coefficient actions.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v

namespace ModuleCat.Algebra.Hochschild.Matrix

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]

local notation "Cλ" => ModuleCat.Algebra.Hochschild.NonUnital.connesComplex
local notation "D" => ModuleCat.Algebra.Hochschild.NonUnital.cyclicBicomplex

/-- The projection from the regular tensor term to its Connes cokernel. -/
abbrev connesProjection (n : ℕ) :
    ModuleCat.Algebra.Hochschild.chainLevel k A A n ⟶ (Cλ k A).X n :=
  (cokernel.π ((D k A).d 1 0)).f n

/-- Evaluation of the original cokernel projection is an epimorphism. -/
instance connesProjection_epi (n : ℕ) : Epi (connesProjection k A n) := by
  let E := HomologicalComplex.eval (ModuleCat.{max u v} k) (ComplexShape.down ℕ) n
  change Epi (E.map (cokernel.π ((D k A).d 1 0)))
  infer_instance

/-- The native Connes projection annihilates the original signed cyclic relation. -/
theorem connesProjection_oneSubCyclic (n : ℕ) :
    ModuleCat.ofHom (1 - TensorPower.consCyclicOperator k A n) ≫
      connesProjection k A n = 0 := by
  have h := congrArg (fun f => f.f n) (cokernel.condition ((D k A).d 1 0))
  change ((D k A).d 1 0).f n ≫ connesProjection k A n = 0 at h
  have hd := ModuleCat.Algebra.Hochschild.NonUnital.connesComplex_levelMap k A n
  exact (congrArg (fun d => ModuleCat.ofHom d ≫ connesProjection k A n) hd).symm.trans h

/-- The cokernel projection commutes with the original full Hochschild boundary. -/
theorem connesProjection_boundary (n : ℕ) :
    connesProjection k A (n + 1) ≫ (Cλ k A).d (n + 1) n =
      (ModuleCat.Algebra.Hochschild.NonUnital.bComplex k A).d (n + 1) n ≫
        connesProjection k A n := by
  exact (cokernel.π ((D k A).d 1 0)).comm (n + 1) n

/-- The projected original regular tensor representative. -/
def connesRepresentative (n : ℕ) : A ⊗[k] TensorPower k n A →ₗ[k] (Cλ k A).X n :=
  (connesProjection k A n).hom

/-- The native representative agrees with its signed last-to-first rotation. -/
theorem connesRepresentative_cyclic (n : ℕ) (x : A ⊗[k] TensorPower k n A) :
    connesRepresentative k A n (TensorPower.consCyclicOperator k A n x) =
      connesRepresentative k A n x := by
  have h := congrArg (fun f => f.hom x) (connesProjection_oneSubCyclic k A n)
  change connesRepresentative k A n (x - TensorPower.consCyclicOperator k A n x) = 0 at h
  rw [map_sub, sub_eq_zero] at h
  exact h.symm

/-- Every nonnegative signed cyclic power has the same Connes representative. -/
theorem connesRepresentative_cyclic_pow (n j : ℕ) (x : A ⊗[k] TensorPower k n A) :
    connesRepresentative k A n ((TensorPower.consCyclicOperator k A n ^ j) x) =
      connesRepresentative k A n x := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply,
        connesRepresentative_cyclic, ih]

/-- A whole tensor-power representative uses the native cons equivalence. -/
def connesTensorRepresentative (n : ℕ) : TensorPower k (n + 1) A →ₗ[k] (Cλ k A).X n :=
  (connesRepresentative k A n).comp (TensorPower.consEquiv k A n).symm.toLinearMap

/-- The signed last-to-first rotation law on the original full tensor power. -/
theorem connesTensorRepresentative_cyclic (n : ℕ) (x : TensorPower k (n + 1) A) :
    connesTensorRepresentative k A n (TensorPower.cyclicOperator k A n x) =
      connesTensorRepresentative k A n x := by
  have h := connesRepresentative_cyclic k A n ((TensorPower.consEquiv k A n).symm x)
  have hc := TensorPower.consCyclicOperator_coordinates k A n
    ((TensorPower.consEquiv k A n).symm x)
  rw [LinearEquiv.apply_symm_apply] at hc
  have hc' := congrArg (fun y => connesRepresentative k A n
    ((TensorPower.consEquiv k A n).symm y)) hc
  simp only [LinearEquiv.symm_apply_apply] at hc'
  exact hc'.symm.trans h

/-- Every full tensor representative is invariant under all signed cyclic powers. -/
theorem connesTensorRepresentative_cyclic_pow (n j : ℕ)
    (x : TensorPower k (n + 1) A) :
    connesTensorRepresentative k A n ((TensorPower.cyclicOperator k A n ^ j) x) =
      connesTensorRepresentative k A n x := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply,
        connesTensorRepresentative_cyclic, ih]

section Naturality

variable {B : Type v} [Ring B] [Algebra k B]

/-- The Connes map retains the original coefficient map before quotient projection. -/
theorem connesProjection_natural (f : A →ₙₐ[k] B) (n : ℕ) :
    connesProjection k A n ≫
        (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom f).f n =
      ModuleCat.ofHom (TensorPower.consLevelMap (f : A →ₗ[k] B) n) ≫ connesProjection k B n := by
  have h := congrArg (fun g => g.f n)
    (HomologicalComplex₂.firstColumnCokernelMap_π
      (ModuleCat.Algebra.Hochschild.NonUnital.cyclicBicomplexHom f))
  simp only [HomologicalComplex.comp_f] at h
  change (cokernel.π ((D k A).d 1 0)).f n ≫
      (HomologicalComplex₂.firstColumnCokernelMap
        (ModuleCat.Algebra.Hochschild.NonUnital.cyclicBicomplexHom f)).f n =
    ModuleCat.ofHom (TensorPower.consLevelMap (f : A →ₗ[k] B) n) ≫
      (cokernel.π ((D k B).d 1 0)).f n
  exact h.trans (by
    rw [ModuleCat.Algebra.Hochschild.NonUnital.cyclicBicomplexHom_f_f]
    rfl)

/-- Coefficient functoriality on every pure tensor representative. -/
theorem connesTensorRepresentative_natural (f : A →ₙₐ[k] B) (n : ℕ)
    (x : TensorPower k (n + 1) A) :
    ((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom f).f n).hom
        (connesTensorRepresentative k A n x) =
      connesTensorRepresentative k B n
        (PiTensorProduct.map (fun _ : Fin (n + 1) => (f : A →ₗ[k] B)) x) := by
  have h := congrArg (fun g => g.hom ((TensorPower.consEquiv k A n).symm x))
    (connesProjection_natural k A f n)
  have hc := LinearMap.congr_fun (TensorPower.consEquiv_naturality (f : A →ₗ[k] B) n)
    ((TensorPower.consEquiv k A n).symm x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hc
  rw [LinearEquiv.apply_symm_apply] at hc
  have hc' := congrArg (fun y => connesRepresentative k B n
    ((TensorPower.consEquiv k B n).symm y)) hc
  simp only [LinearEquiv.symm_apply_apply] at hc'
  exact h.trans hc'

end Naturality

/-- The full native trace followed by the target Connes projection. -/
def connesTraceRepresentative (r n : ℕ) :
    Matrix (Fin r) (Fin r) A ⊗[k] TensorPower k n (Matrix (Fin r) (Fin r) A) →ₗ[k]
      (Cλ k A).X n :=
  (connesRepresentative k A n).comp (generalizedTrace k (Fin r) n)

/-- The same projected trace with the cyclic degree objects as endpoints. -/
def connesTraceRepresentativeMap (r n : ℕ) :
    ((D k (Matrix (Fin r) (Fin r) A)).X 0).X n ⟶ (Cλ k A).X n :=
  ModuleCat.ofHom (connesTraceRepresentative k A r n)

/-- The original regular matrix and scalar faces retain the trace square. -/
theorem trace_regularFace (r n : ℕ) (i : Fin (n + 2)) :
    (generalizedTrace k (Fin r) n).comp
        (ModuleCat.Algebra.Hochschild.NonUnital.regularFace k
          (Matrix (Fin r) (Fin r) A) n i).hom =
      (ModuleCat.Algebra.Hochschild.NonUnital.regularFace k A n i).hom.comp
        (generalizedTrace k (Fin r) (n + 1)) := by
  have hself : (Coefficients.face A A (Fin r) k n i).hom =
      (ModuleCat.Algebra.Hochschild.NonUnital.regularFace k
        (Matrix (Fin r) (Fin r) A) n i).hom := by
    dsimp only [Coefficients.face]
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro X a
    refine Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun l => ?_) j) i
    · rw [ModuleCat.Algebra.Hochschild.face_first_tprod,
        ModuleCat.Algebra.Hochschild.NonUnital.regularFace_first_tprod]
      have hr :
          letI : Module (Matrix (Fin r) (Fin r) A)ᵐᵒᵖ (Matrix (Fin r) (Fin r) A) :=
            Coefficients.rightModule A A (Fin r)
          MulOpposite.op (a 0) • X = X * a 0 := by
        rw [Coefficients.rightModule_self_eq]
        rfl
      exact congrArg (fun y => y ⊗ₜ[k] PiTensorProduct.tprod k (hochschildDropFirst a)) hr
    · rw [Fin.succ_last, ModuleCat.Algebra.Hochschild.face_last_tprod,
        ModuleCat.Algebra.Hochschild.NonUnital.regularFace_last_tprod]
      have hl :
          @SMul.smul (Matrix (Fin r) (Fin r) A) (Matrix (Fin r) (Fin r) A)
            (Coefficients.leftModule A A (Fin r)).toDistribMulAction.toMulAction.toSMul
            (a (Fin.last n)) X = a (Fin.last n) * X := by
        exact congrArg
          (fun ρ : Module (Matrix (Fin r) (Fin r) A) (Matrix (Fin r) (Fin r) A) =>
            @SMul.smul (Matrix (Fin r) (Fin r) A) (Matrix (Fin r) (Fin r) A)
              ρ.toDistribMulAction.toMulAction.toSMul (a (Fin.last n)) X)
          (Coefficients.leftModule_self_eq A (Fin r))
      exact congrArg (fun y => y ⊗ₜ[k] PiTensorProduct.tprod k (hochschildDropLast a)) hl
    · rw [ModuleCat.Algebra.Hochschild.face_inner_tprod,
        ModuleCat.Algebra.Hochschild.NonUnital.regularFace_inner_tprod]
  have htarget : (ModuleCat.Algebra.Hochschild.face k A A n i).hom =
      (ModuleCat.Algebra.Hochschild.NonUnital.regularFace k A n i).hom := by
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro x a
    refine Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun l => ?_) j) i
    · rw [ModuleCat.Algebra.Hochschild.face_first_tprod,
        ModuleCat.Algebra.Hochschild.NonUnital.regularFace_first_tprod]
      rfl
    · rw [Fin.succ_last, ModuleCat.Algebra.Hochschild.face_last_tprod,
        ModuleCat.Algebra.Hochschild.NonUnital.regularFace_last_tprod]
      rfl
    · rw [ModuleCat.Algebra.Hochschild.face_inner_tprod,
        ModuleCat.Algebra.Hochschild.NonUnital.regularFace_inner_tprod]
  exact ((congrArg (fun f => (generalizedTrace k (Fin r) n).comp f) hself).symm.trans
    (trace_face_comm k A A (Fin r) n i)).trans
      (congrArg (fun f => f.comp (generalizedTrace k (Fin r) (n + 1))) htarget)

/-- The full original signed regular boundary, including its cyclic last face, commutes with trace. -/
theorem trace_regularBoundary (r n : ℕ) :
    (generalizedTrace k (Fin r) n).comp
        ((ModuleCat.Algebra.Hochschild.NonUnital.bComplex k
          (Matrix (Fin r) (Fin r) A)).d (n + 1) n).hom =
      ((ModuleCat.Algebra.Hochschild.NonUnital.bComplex k A).d (n + 1) n).hom.comp
        (generalizedTrace k (Fin r) (n + 1)) := by
  have hS := congrArg (fun f => f.hom)
    (ModuleCat.Algebra.Hochschild.NonUnital.bComplex_d k (Matrix (Fin r) (Fin r) A) n)
  have hT := congrArg (fun f => f.hom)
    (ModuleCat.Algebra.Hochschild.NonUnital.bComplex_d k A n)
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul] at hS hT
  rw [hS, hT]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun z => (-1 : ℤ) ^ i.val • z)
    (LinearMap.congr_fun (trace_regularFace k A r n i) x)

/-- The cyclic trace square kills the source Connes relation. -/
theorem connesTraceRepresentative_oneSub (r n : ℕ) :
    (connesTraceRepresentative k A r n).comp
      (1 - TensorPower.consCyclicOperator k (Matrix (Fin r) (Fin r) A) n) = 0 := by
  apply LinearMap.ext
  intro x
  change connesRepresentative k A n
      (generalizedTrace k (Fin r) n
        (x - TensorPower.consCyclicOperator k (Matrix (Fin r) (Fin r) A) n x)) = 0
  rw [map_sub, map_sub]
  have ht := LinearMap.congr_fun (generalizedTrace_cyclic k A (Fin r) n) x
  simp only [LinearMap.comp_apply] at ht
  rw [← ht, connesRepresentative_cyclic, sub_self]

/-- The degree trace between the Connes cokernels. -/
def connesTraceComponent (r n : ℕ) : (Cλ k (Matrix (Fin r) (Fin r) A)).X n ⟶ (Cλ k A).X n :=
  (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexXIsoCokernel
      k (Matrix (Fin r) (Fin r) A) n).hom ≫
    cokernel.desc (((D k (Matrix (Fin r) (Fin r) A)).d 1 0).f n)
      (connesTraceRepresentativeMap k A r n) (by
        apply ModuleCat.hom_ext
        have h := ModuleCat.Algebra.Hochschild.NonUnital.connesComplex_levelMap
          k (Matrix (Fin r) (Fin r) A) n
        exact (congrArg (fun d => (connesTraceRepresentative k A r n).comp d) h).trans
          (connesTraceRepresentative_oneSub k A r n))

/-- The native source projection retains the exact original full trace representative. -/
theorem connesProjection_traceComponent (r n : ℕ) :
    connesProjection k (Matrix (Fin r) (Fin r) A) n ≫ connesTraceComponent k A r n =
      connesTraceRepresentativeMap k A r n := by
  let f := (D k (Matrix (Fin r) (Fin r) A)).d 1 0
  let E := HomologicalComplex.eval (ModuleCat.{max u v} k) (ComplexShape.down ℕ) n
  let e := asIso (cokernelComparison f E)
  have h : cokernel.π (E.map f) ≫ e.hom = E.map (cokernel.π f) :=
    π_comp_cokernelComparison f E
  have hp : E.map (cokernel.π f) ≫ e.inv = cokernel.π (E.map f) := by
    exact (congrArg (fun p => p ≫ e.inv) h.symm).trans
      ((Category.assoc _ _ _).trans ((congrArg
        (fun a => cokernel.π (E.map f) ≫ a) e.hom_inv_id).trans (Category.comp_id _)))
  change E.map (cokernel.π f) ≫ (e.inv ≫ _) = _
  rw [← Category.assoc, hp]
  change cokernel.π (((D k (Matrix (Fin r) (Fin r) A)).d 1 0).f n) ≫
      cokernel.desc (((D k (Matrix (Fin r) (Fin r) A)).d 1 0).f n)
        (connesTraceRepresentativeMap k A r n) _ = _
  exact cokernel.π_desc _ _ _

/-- The native Connes trace has the regular tensor representative formula. -/
theorem connesTraceComponent_tprod (r n : ℕ) (X : Matrix (Fin r) (Fin r) A)
    (a : Fin n → Matrix (Fin r) (Fin r) A) :
    (connesTraceComponent k A r n).hom
      ((connesProjection k (Matrix (Fin r) (Fin r) A) n).hom
        (X ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      ∑ γ : Fin (n + 1) → Fin r, connesRepresentative k A n
        (X (γ 0) (γ 1) ⊗ₜ[k] PiTensorProduct.tprod k
          (fun j => a j (γ j.succ) (γ (j.succ + 1)))) := by
  have h := congrArg (fun f => f.hom (X ⊗ₜ[k] PiTensorProduct.tprod k a))
    (connesProjection_traceComponent k A r n)
  exact h.trans (by
    change connesRepresentative k A n
      (generalizedTrace k (Fin r) n (X ⊗ₜ[k] PiTensorProduct.tprod k a)) = _
    rw [generalizedTrace_tmul_tprod, map_sum])

/-- The trace descends as a chain map of the Connes complexes. -/
def connesTrace (r : ℕ) : Cλ k (Matrix (Fin r) (Fin r) A) ⟶ Cλ k A :=
  ChainComplex.ofHom (connesTraceComponent k A r) (by
    intro n
    apply (cancel_epi (connesProjection k (Matrix (Fin r) (Fin r) A) (n + 1))).1
    have hS := connesProjection_boundary k (Matrix (Fin r) (Fin r) A) n
    have hC₁ := connesProjection_traceComponent k A r (n + 1)
    have hC₀ := connesProjection_traceComponent k A r n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hvS := congrArg (fun f => f.hom x) hS
    have hvC₁ := congrArg (fun f => f.hom x) hC₁
    have hvC₀ := congrArg (fun f => f.hom
      (((ModuleCat.Algebra.Hochschild.NonUnital.bComplex k
        (Matrix (Fin r) (Fin r) A)).d (n + 1) n).hom x)) hC₀
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hvS hvC₁ hvC₀
    change ((Cλ k A).d (n + 1) n).hom
        ((connesTraceComponent k A r (n + 1)).hom
          ((connesProjection k (Matrix (Fin r) (Fin r) A) (n + 1)).hom x)) =
      (connesTraceComponent k A r n).hom
        (((Cλ k (Matrix (Fin r) (Fin r) A)).d (n + 1) n).hom
          ((connesProjection k (Matrix (Fin r) (Fin r) A) (n + 1)).hom x))
    rw [hvC₁, hvS, hvC₀]
    change ((Cλ k A).d (n + 1) n).hom
        (connesRepresentative k A (n + 1) (generalizedTrace k (Fin r) (n + 1) x)) =
      connesRepresentative k A n (generalizedTrace k (Fin r) n
        (((ModuleCat.Algebra.Hochschild.NonUnital.bComplex k
          (Matrix (Fin r) (Fin r) A)).d (n + 1) n).hom x))
    have hp := congrArg (fun f => f.hom) (connesProjection_boundary k A n)
    simp only [ModuleCat.hom_comp] at hp
    have ht := trace_regularBoundary k A r n
    exact (LinearMap.congr_fun hp (generalizedTrace k (Fin r) (n + 1) x)).trans
      (congrArg (connesRepresentative k A n) (LinearMap.congr_fun ht x).symm))

/-- The chain-map component is the constructed native Connes trace component. -/
theorem connesTrace_f (r n : ℕ) : (connesTrace k A r).f n = connesTraceComponent k A r n := rfl

/-- Actual zero corners induce the native Connes quotient map. -/
def connesZeroCorner {r s : ℕ} (h : r ≤ s) :
    Cλ k (Matrix (Fin r) (Fin r) A) ⟶ Cλ k (Matrix (Fin s) (Fin s) A) :=
  ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom
    (Matrix.zeroExtendAlgHom (k := k) (A := A) h)

/-- The native zero-corner projection square has the original tensor-coordinate map. -/
theorem connesProjection_zeroCorner {r s : ℕ} (h : r ≤ s) (n : ℕ) :
    connesProjection k (Matrix (Fin r) (Fin r) A) n ≫ (connesZeroCorner k A h).f n =
      ModuleCat.ofHom (TensorPower.consLevelMap (Matrix.zeroExtendLinear (k := k) (A := A) h) n) ≫
        connesProjection k (Matrix (Fin s) (Fin s) A) n := by
  have hπ := congrArg (fun f => f.f n)
    (HomologicalComplex₂.firstColumnCokernelMap_π
      (ModuleCat.Algebra.Hochschild.NonUnital.cyclicBicomplexHom
        (Matrix.zeroExtendAlgHom (k := k) (A := A) h)))
  simp only [HomologicalComplex.comp_f] at hπ
  change (cokernel.π ((D k (Matrix (Fin r) (Fin r) A)).d 1 0)).f n ≫
      (HomologicalComplex₂.firstColumnCokernelMap
        (ModuleCat.Algebra.Hochschild.NonUnital.cyclicBicomplexHom
          (Matrix.zeroExtendAlgHom (k := k) (A := A) h))).f n = _
  exact hπ.trans (by
    rw [ModuleCat.Algebra.Hochschild.NonUnital.cyclicBicomplexHom_f_f]
    rfl)

/-- The full Connes trace is stable under every original finite zero corner. -/
theorem connesZeroCorner_trace {r s : ℕ} (h : r ≤ s) :
    connesZeroCorner k A h ≫ connesTrace k A s = connesTrace k A r := by
  apply HomologicalComplex.hom_ext
  intro n
  apply (cancel_epi (connesProjection k (Matrix (Fin r) (Fin r) A) n)).1
  rw [HomologicalComplex.comp_f, connesTrace_f, connesTrace_f,
    ← Category.assoc, connesProjection_zeroCorner,
    Category.assoc, connesProjection_traceComponent, connesProjection_traceComponent]
  apply ModuleCat.hom_ext
  change (connesTraceRepresentative k A s n).comp
      (TensorPower.consLevelMap (Matrix.zeroExtendLinear (k := k) (A := A) h) n) =
    connesTraceRepresentative k A r n
  rw [connesTraceRepresentative, connesTraceRepresentative, LinearMap.comp_assoc]
  exact congrArg (fun f => (connesRepresentative k A n).comp f)
    (generalizedTrace_comp_zeroExtend k h n)

section CoefficientNaturality

variable {B : Type v} [Ring B] [Algebra k B]

/-- The matrix coefficient map on native Connes complexes. -/
def connesMatrixCoefficientMap (f : A →ₐ[k] B) (r : ℕ) :
    Cλ k (Matrix (Fin r) (Fin r) A) ⟶ Cλ k (Matrix (Fin r) (Fin r) B) :=
  ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom
    (f.mapMatrix (m := Fin r)).toNonUnitalAlgHom

/-- Every coefficient map commutes with the full native Connes trace. -/
theorem connesTrace_natural (f : A →ₐ[k] B) (r : ℕ) :
    connesMatrixCoefficientMap k A f r ≫ connesTrace k B r =
      connesTrace k A r ≫ ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom f.toNonUnitalAlgHom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply (cancel_epi (connesProjection k (Matrix (Fin r) (Fin r) A) n)).1
  change connesProjection k (Matrix (Fin r) (Fin r) A) n ≫
      ((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom
        (f.mapMatrix (m := Fin r)).toNonUnitalAlgHom).f n ≫ connesTraceComponent k B r n) =
    connesProjection k (Matrix (Fin r) (Fin r) A) n ≫
      (connesTraceComponent k A r n ≫
        (ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom f.toNonUnitalAlgHom).f n)
  rw [← Category.assoc,
    connesProjection_natural, Category.assoc, connesProjection_traceComponent,
    ← Category.assoc, connesProjection_traceComponent]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro X
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro a
  have ht := LinearMap.congr_fun
    (generalizedTrace_naturality k (Fin r) n f.toLinearMap f.toLinearMap)
    (X ⊗ₜ[k] PiTensorProduct.tprod k a)
  simp only [LinearMap.comp_apply] at ht
  have hp := congrArg (fun g => g.hom
      (generalizedTrace k (Fin r) n (X ⊗ₜ[k] PiTensorProduct.tprod k a)))
    (connesProjection_natural k A f.toNonUnitalAlgHom n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hp
  change connesRepresentative k B n
      (generalizedTrace k (Fin r) n
        (TensorProduct.map f.toLinearMap.mapMatrix
          (PiTensorProduct.map fun _ : Fin n => f.toLinearMap.mapMatrix)
          (X ⊗ₜ[k] PiTensorProduct.tprod k a))) =
    ((ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom f.toNonUnitalAlgHom).f n).hom
      (connesRepresentative k A n
        (generalizedTrace k (Fin r) n (X ⊗ₜ[k] PiTensorProduct.tprod k a)))
  exact (congrArg (connesRepresentative k B n) ht).symm.trans hp.symm

end CoefficientNaturality

end ModuleCat.Algebra.Hochschild.Matrix

end
