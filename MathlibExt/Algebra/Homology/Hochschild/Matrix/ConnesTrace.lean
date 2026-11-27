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
# Generalized matrix trace on the signed cyclic quotient

Let k be a commutative ring and A an associative unital k-algebra. Put
C_n(A) = A ⊗[k] A^⊗n and
t_n(a₀ ⊗ ⋯ ⊗ aₙ) = (−1)^n aₙ ⊗ a₀ ⊗ ⋯ ⊗ a_(n−1).
The Connes quotient complex Cλ(A) is the cokernel of the first-column
map in the cyclic bicomplex. Its degree-n projection q_n annihilates
1−t_n, so [x] = [t_n x], and its differential is induced by the full
Hochschild boundary b = ∑ᵢ(−1)^i δᵢ.

For r ≥ 0, the closed-cycle generalized trace from r×r matrices over A
commutes with both b and t. It therefore gives a chain map
T : Cλ(Mat_r(A)) → Cλ(A) with the representative formula
T_n([X ⊗ a₁ ⊗ ⋯ ⊗ aₙ]) =
∑_(i₀,…,iₙ) [X_(i₀,i₁) ⊗ (a₁)_(i₁,i₂) ⊗ ⋯ ⊗ (aₙ)_(iₙ,i₀)].
Top-left zero extensions preserve this map, and unital k-algebra maps
commute with it. The projection squares also hold for nonunital
k-algebra maps. These statements hold over arbitrary k, with no
inversion of integers.
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

/-- For a commutative ring k and a k-algebra A, the projection
q_n : C_n(A) → Cλ_n(A) is the degree-n component of the cokernel
projection from the zeroth column of the cyclic bicomplex. Here
C_n(A) = A ⊗[k] A^⊗n, and the cokernel relation is 1−t_n for the
signed last-to-first cyclic operator t_n. -/
abbrev connesProjection (n : ℕ) :
    ModuleCat.Algebra.Hochschild.chainLevel k A A n ⟶ (Cλ k A).X n :=
  (cokernel.π ((D k A).d 1 0)).f n

/-- For a commutative ring k, a k-algebra A and n ≥ 0, the
projection q_n : C_n(A) → Cλ_n(A) is an epimorphism of k-modules.
Thus every element of the degree-n Connes quotient has a tensor
representative. -/
instance connesProjection_epi (n : ℕ) : Epi (connesProjection k A n) := by
  let E := HomologicalComplex.eval (ModuleCat.{max u v} k) (ComplexShape.down ℕ) n
  change Epi (E.map (cokernel.π ((D k A).d 1 0)))
  infer_instance

/-- For a k-algebra A and every n ≥ 0, the degree projection
q_n : C_n(A) → Cλ_n(A) satisfies q_n ∘ (1−t_n) = 0.
Here t_n(a₀ ⊗ ⋯ ⊗ aₙ) =
(−1)^n aₙ ⊗ a₀ ⊗ ⋯ ⊗ a_(n−1). -/
theorem connesProjection_oneSubCyclic (n : ℕ) :
    ModuleCat.ofHom (1 - TensorPower.consCyclicOperator k A n) ≫
      connesProjection k A n = 0 := by
  have h := congrArg (fun f => f.f n) (cokernel.condition ((D k A).d 1 0))
  change ((D k A).d 1 0).f n ≫ connesProjection k A n = 0 at h
  have hd := ModuleCat.Algebra.Hochschild.NonUnital.connesComplex_levelMap k A n
  exact (congrArg (fun d => ModuleCat.ofHom d ≫ connesProjection k A n) hd).symm.trans h

/-- For a k-algebra A, the full Hochschild boundary
b_n : C_(n+1)(A) → C_n(A) and the quotient differential
d_n : Cλ_(n+1)(A) → Cλ_n(A) satisfy
d_n ∘ q_(n+1) = q_n ∘ b_n for every n ≥ 0.
The boundary b_n includes the cyclic last face. -/
theorem connesProjection_boundary (n : ℕ) :
    connesProjection k A (n + 1) ≫ (Cλ k A).d (n + 1) n =
      (ModuleCat.Algebra.Hochschild.NonUnital.bComplex k A).d (n + 1) n ≫
        connesProjection k A n := by
  exact (cokernel.π ((D k A).d 1 0)).comm (n + 1) n

/-- For a k-algebra A, the k-linear representative map
C_n(A) = A ⊗[k] A^⊗n → Cλ_n(A) sends a tensor x to its class [x]
in the signed cyclic quotient, where [x−t_n x] = 0. -/
def connesRepresentative (n : ℕ) : A ⊗[k] TensorPower k n A →ₗ[k] (Cλ k A).X n :=
  (connesProjection k A n).hom

/-- For a k-algebra A, n ≥ 0 and x ∈ A ⊗[k] A^⊗n, the Connes
classes satisfy [t_n x] = [x], with t_n the last-to-first rotation
multiplied by (−1)^n. -/
theorem connesRepresentative_cyclic (n : ℕ) (x : A ⊗[k] TensorPower k n A) :
    connesRepresentative k A n (TensorPower.consCyclicOperator k A n x) =
      connesRepresentative k A n x := by
  have h := congrArg (fun f => f.hom x) (connesProjection_oneSubCyclic k A n)
  change connesRepresentative k A n (x - TensorPower.consCyclicOperator k A n x) = 0 at h
  rw [map_sub, sub_eq_zero] at h
  exact h.symm

/-- For a k-algebra A, n,j ≥ 0 and x ∈ A ⊗[k] A^⊗n, the
Connes classes satisfy [t_n^j x] = [x]. The cyclic operator t_n
includes the sign (−1)^n. -/
theorem connesRepresentative_cyclic_pow (n j : ℕ) (x : A ⊗[k] TensorPower k n A) :
    connesRepresentative k A n ((TensorPower.consCyclicOperator k A n ^ j) x) =
      connesRepresentative k A n x := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply,
        connesRepresentative_cyclic, ih]

/-- For a k-algebra A and n ≥ 0, the k-linear map
A^⊗(n+1) → Cλ_n(A) separates the first tensor factor and then takes
the Connes class. On a pure tensor it sends
a₀ ⊗ ⋯ ⊗ aₙ to [a₀ ⊗ (a₁ ⊗ ⋯ ⊗ aₙ)]. -/
def connesTensorRepresentative (n : ℕ) : TensorPower k (n + 1) A →ₗ[k] (Cλ k A).X n :=
  (connesRepresentative k A n).comp (TensorPower.consEquiv k A n).symm.toLinearMap

/-- For a k-algebra A and x ∈ A^⊗(n+1), taking its Connes
representative after the signed last-to-first rotation gives the
same class as taking the representative of x. The rotation sign
is (−1)^n. -/
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

/-- For a k-algebra A, n,j ≥ 0 and x ∈ A^⊗(n+1), the Connes
representative of t_n^j x equals that of x, where t_n rotates the
full tensor power with sign (−1)^n. -/
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

/-- For k-algebras A and B in the same carrier universe and a
nonunital k-algebra map f : A → B, applying f to all n+1 factors
and then projecting to Cλ_n(B) equals projecting to Cλ_n(A) and then
applying the induced Connes map. Thus
Cλ_n(f) ∘ q_n^A = q_n^B ∘ (f ⊗ f^⊗n). -/
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

/-- For k-algebras A and B in the same carrier universe, a
nonunital k-algebra map f : A → B and x ∈ A^⊗(n+1), the induced
Connes map sends the representative of x to the representative of
f^⊗(n+1)(x) in Cλ_n(B). The formula holds for every tensor-power
element x. -/
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

/-- For a k-algebra A and r,n ≥ 0, the k-linear map
C_n(Mat_r(A)) → Cλ_n(A) sends x to [T_n(x)], where T_n is the
closed-cycle generalized matrix trace. The coefficient module here
is the regular module A. -/
def connesTraceRepresentative (r n : ℕ) :
    Matrix (Fin r) (Fin r) A ⊗[k] TensorPower k n (Matrix (Fin r) (Fin r) A) →ₗ[k]
      (Cλ k A).X n :=
  (connesRepresentative k A n).comp (generalizedTrace k (Fin r) n)

/-- For a k-algebra A and r,n ≥ 0, the map from the degree-n
zeroth column of the matrix cyclic bicomplex to Cλ_n(A) is the
k-module morphism x ↦ [T_n(x)], with T_n the generalized matrix trace. -/
def connesTraceRepresentativeMap (r n : ℕ) :
    ((D k (Matrix (Fin r) (Fin r) A)).X 0).X n ⟶ (Cλ k A).X n :=
  ModuleCat.ofHom (connesTraceRepresentative k A r n)

/-- For a k-algebra A, r,n ≥ 0 and i ∈ {0,…,n+1}, the regular
Hochschild faces satisfy T_n ∘ δᵢ^Mat = δᵢ^A ∘ T_(n+1).
The first face multiplies X a₁, the interior faces multiply adjacent
matrices in their given order, and the last face multiplies a_(n+1) X. -/
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

/-- For a k-algebra A and r,n ≥ 0, the closed-cycle trace satisfies
T_n ∘ b_n^Mat = b_n^A ∘ T_(n+1), where
b_n = ∑_(i=0)^(n+1) (−1)^i δᵢ is the full regular Hochschild boundary,
including the last product a_(n+1)a₀. -/
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

/-- For a k-algebra A and r,n ≥ 0, the map x ↦ [T_n(x)] from
C_n(Mat_r(A)) to Cλ_n(A) annihilates 1−t_n^Mat.
Equivalently, [T_n(x−t_n^Mat x)] = 0 for every matrix tensor x. -/
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

/-- For a k-algebra A and r,n ≥ 0, the generalized trace induces
Tλ_n : Cλ_n(Mat_r(A)) → Cλ_n(A). It is characterized by
Tλ_n([x]) = [T_n(x)] for matrix tensor representatives x. -/
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

/-- For a k-algebra A and r,n ≥ 0, the matrix and scalar
Connes projections satisfy
Tλ_n ∘ q_n^Mat = q_n^A ∘ T_n.
Thus the quotient trace of a projected matrix tensor is the scalar
Connes class of its full generalized trace. -/
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

/-- For a k-algebra A, X ∈ Mat_r(A) and aⱼ ∈ Mat_r(A), the
degree-n quotient trace sends [X ⊗ a₁ ⊗ ⋯ ⊗ aₙ] to
∑_(i₀,…,iₙ) [X_(i₀,i₁) ⊗ (a₁)_(i₁,i₂) ⊗ ⋯ ⊗ (aₙ)_(iₙ,i₀)].
The finite sum ranges over Fin r-valued cycles with indices modulo
n+1; for n = 0 it is the class of the additive matrix trace. -/
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

/-- For a k-algebra A and r ≥ 0, the degree quotient traces
define a chain map Cλ(Mat_r(A)) → Cλ(A). Its differential is induced
by the full regular Hochschild boundary, and its degree-n value is
[x] ↦ [T_n(x)]. -/
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

/-- For a k-algebra A and r,n ≥ 0, the degree-n component of the
Connes quotient trace chain map is the induced quotient morphism
Tλ_n : Cλ_n(Mat_r(A)) → Cλ_n(A), characterized by [x] ↦ [T_n(x)]. -/
theorem connesTrace_f (r n : ℕ) : (connesTrace k A r).f n = connesTraceComponent k A r n := rfl

/-- For a k-algebra A and r ≤ s, top-left extension by zero of
r×r matrices to s×s matrices induces a chain map
Cλ(Mat_r(A)) → Cλ(Mat_s(A)).
It applies zero extension to each tensor factor before taking its class;
the matrix algebra map is allowed to be nonunital. -/
def connesZeroCorner {r s : ℕ} (h : r ≤ s) :
    Cλ k (Matrix (Fin r) (Fin r) A) ⟶ Cλ k (Matrix (Fin s) (Fin s) A) :=
  ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom
    (Matrix.zeroExtendAlgHom (k := k) (A := A) h)

/-- For a k-algebra A, r ≤ s and n ≥ 0, let Z_n apply top-left
zero extension to every factor of C_n(Mat_r(A)). The induced quotient
map Cλ_n(Z) satisfies Cλ_n(Z) ∘ q_n^r = q_n^s ∘ Z_n.
This equality is a square of k-module maps. -/
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

/-- For a k-algebra A and r ≤ s, the zero-extension chain map
Cλ(Mat_r(A)) → Cλ(Mat_s(A)) followed by the size-s trace equals
the size-r trace. Thus Tλ^s ∘ Cλ(Z) = Tλ^r as chain maps, including
the empty stage r = 0. -/
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

/-- For k-algebras A and B in the same carrier universe, a
unital k-algebra map f : A → B and r ≥ 0, entrywise application of f
induces Cλ(Mat_r(A)) → Cλ(Mat_r(B)). Its tensor representatives are
obtained by applying f to every matrix entry in every factor. -/
def connesMatrixCoefficientMap (f : A →ₐ[k] B) (r : ℕ) :
    Cλ k (Matrix (Fin r) (Fin r) A) ⟶ Cλ k (Matrix (Fin r) (Fin r) B) :=
  ModuleCat.Algebra.Hochschild.NonUnital.connesComplexHom
    (f.mapMatrix (m := Fin r)).toNonUnitalAlgHom

/-- For k-algebras A and B in the same carrier universe, a
unital k-algebra map f : A → B and r ≥ 0, the chain-map square
Tλ^B ∘ Cλ(Mat_r(f)) = Cλ(f) ∘ Tλ^A commutes from
Cλ(Mat_r(A)) to Cλ(B). Both paths take a matrix tensor class to the
class of its entrywise-f generalized trace. -/
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
