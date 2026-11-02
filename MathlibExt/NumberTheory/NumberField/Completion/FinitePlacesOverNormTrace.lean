/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.Completion.FinitePlacesOverTensorProductEquiv
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Trace

@[expose] public section

/-!
# Global norm and trace as products and sums over finite-place completions

This file formalizes the number-field specialization of ATLAS `NumberTheoryI`
target N237, Corollary 11.24: for a finite extension `L / K` of number fields,
a finite place `v` of `K`, and `α : L`, the image of the global norm
`Algebra.norm K α` in the completion `K_v` is the product of the local norms
from each completion `L_w` above `v`, and the image of the global trace is the
sum of the local traces. Both local maps share the common base completion
`K_v` (the target YAML's local trace denominator `K_q` is a typographical
error; the primary Lean source uses the common base `K_p` throughout).

This is the number-field specialization of the source's general AKLB wording:
the source works over general Dedekind domains with fraction fields, while
here the base rings are specialized to `𝓞 K` and `𝓞 L`.

Scope: this module proves the full NumberTheoryI:237 target after the documented
number-field specialization; it is not a partial prerequisite stage.

## Source-to-API map

At atlas-lean revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, see
`targets.yaml` lines 1685--1693 and the primary Lean source
[`LocalGlobal.lean`, lines 1111--1435](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean#L1111-L1435):

- `commKvAlgEquiv`, `norm_baseChange_eq`, `trace_baseChange_eq` (source lines
  1115--1165) become the private scalar base-change lemmas `norm_scalar_baseChange`
  and `trace_scalar_baseChange` below; the ad hoc tensor commutation is replaced
  by `Algebra.TensorProduct.commRight`.
- `finSuccLinearEquiv'`, `norm_pi_fin'`, `Algebra.norm_pi_apply'`,
  `trace_single_comp_aux`, `pi_lmul_decomp_aux`, `Algebra.trace_pi_apply'`
  (source lines 1167--1328) become the private dependent-Pi evaluation helpers.
- `norm_pi_eq_prod`, `trace_pi_eq_sum` (source lines 1239--1382) are folded into
  the endpoint proofs; the identity wrapper `algEquiv_tmul_one_component`
  (source lines 1222--1237) is dropped and its coordinate law is taken directly
  from `completionTensorProductRightAlgEquiv_tmul_one`.
- `norm_eq_prod_localNorm`, `trace_eq_sum_localTrace` (source lines
  1384--1418) become `algebraMap_norm_eq_prod_adicCompletion` and
  `algebraMap_trace_eq_sum_adicCompletion`. The source's trivial conjunction
  alias `norm_trace_completion_decomposition` (source lines 1420--1435) is not
  reproduced; the two endpoint theorems jointly cover the statement.
- The source's existential tensor-product equivalence
  `theorem_13_5_finite_place_Kv` is replaced by the merged explicit
  `completionTensorProductRightAlgEquiv` and its coordinate theorem
  `completionTensorProductRightAlgEquiv_tmul_one`.
-/

namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField
open scoped NumberField.LiesOver
open scoped TensorProduct
open scoped IsDedekindDomain.HeightOneSpectrum.CompletionTensorProduct

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ## Private dependent-Pi norm helpers (source-shaped) -/

/-- Split a dependent function over `Fin (n + 1)` into head and tail. -/
private def finSuccLinearEquiv' (R : Type*) [CommRing R] {n : ℕ}
    (A : Fin (n + 1) → Type*)
    [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)] :
    (∀ i : Fin (n + 1), A i) ≃ₗ[R] A 0 × (∀ i : Fin n, A (Fin.succ i)) where
  toFun f := (f 0, Fin.tail f)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by ext i; exact congr_fun (Fin.cons_self_tail f) i
  right_inv p := by
    ext
    · exact Fin.cons_zero p.1 p.2
    · exact Fin.cons_succ p.1 p.2 _
  map_add' f g := by ext <;> rfl
  map_smul' r f := by ext <;> rfl

/-- Norm over a `Fin n`-indexed dependent product is the product of norms. -/
private lemma norm_pi_fin' {R : Type*} [CommRing R]
    {n : ℕ} {A : Fin n → Type*}
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
    (f : ∀ i, A i) :
    Algebra.norm R f = ∏ i, Algebra.norm R (f i) := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact (congr_arg _ (Subsingleton.elim f 1)).trans (map_one _)
  | succ n ih =>
    let e := finSuccLinearEquiv' R A
    have step1 : Algebra.norm R f =
        LinearMap.det (e.toLinearMap ∘ₗ (Algebra.lmul R _ f) ∘ₗ
          e.symm.toLinearMap) := by
      rw [LinearMap.det_conj, Algebra.norm_apply]
    have hmul : e.toLinearMap ∘ₗ (Algebra.lmul R _ f) ∘ₗ e.symm.toLinearMap =
        ((Algebra.lmul R (A 0)) (f 0)).prodMap
          ((Algebra.lmul R _) (Fin.tail f)) := by
      apply LinearMap.ext; intro ⟨a, g⟩
      change e (f * e.symm (a, g)) = (f 0 * a, Fin.tail f * g)
      simp only [e, finSuccLinearEquiv', LinearEquiv.coe_mk]
      ext
      · simp [Pi.mul_apply, Fin.cons_zero]
      · simp [Pi.mul_apply, Fin.tail, Fin.cons_succ]
    rw [step1, hmul, LinearMap.det_prodMap, ← Algebra.norm_apply,
      ← Algebra.norm_apply, ih (Fin.tail f), Fin.prod_univ_succ]
    simp only [Fin.tail]

/-- Norm over a finite dependent product is the product of the norms. -/
private theorem norm_pi_apply {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
    (f : ∀ i, A i) :
    (Algebra.norm R) f = ∏ i, (Algebra.norm R) (f i) := by
  classical
  let e := Fintype.equivFin ι
  let φ := AlgEquiv.piCongrLeft R A e.symm
  have h1 : Algebra.norm R f = Algebra.norm R (φ.symm f) := by
    conv_lhs => rw [← φ.apply_symm_apply f]
    exact Algebra.norm_eq_of_algEquiv φ (φ.symm f)
  rw [h1, norm_pi_fin' (φ.symm f)]
  exact Fintype.prod_equiv e.symm _ _ (fun j => by congr 1)

/-! ## Private dependent-Pi trace helpers (source-shaped) -/

set_option linter.unusedFintypeInType false in
/-- Trace of a single embedded component recovers the component trace. -/
private lemma trace_single_comp_aux {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
    (j : ι) (f : A j →ₗ[R] A j) :
    (LinearMap.trace R (∀ i, A i))
        ((LinearMap.single R A j) ∘ₗ (f ∘ₗ (LinearMap.proj j))) =
      (LinearMap.trace R (A j)) f := by
  rw [LinearMap.trace_comp_comm' (f ∘ₗ LinearMap.proj j) (LinearMap.single R A j)]
  congr 1; ext x
  simp [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply]

/-- Multiplication on a dependent product decomposes as a sum of components. -/
private lemma pi_lmul_decomp_aux {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    (f : ∀ i, A i) :
    (Algebra.lmul R (∀ i, A i) f) =
      ∑ i : ι, (LinearMap.single R A i).comp
        ((Algebra.lmul R (A i) (f i)).comp (LinearMap.proj i)) := by
  apply LinearMap.ext; intro x; funext k
  simp only [LinearMap.comp_apply, LinearMap.proj_apply,
    LinearMap.coe_sum, Finset.sum_apply, Finset.sum_apply]
  rw [Finset.sum_eq_single k (fun b _ hbk => ?_) (fun hk => ?_)]
  · simp [LinearMap.single_apply]
  · simp [LinearMap.single_apply, hbk]
  · exact absurd (Finset.mem_univ k) hk

/-- Trace over a finite dependent product is the sum of the traces. -/
private theorem trace_pi_apply {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι]
    {A : ι → Type*} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]
    (f : ∀ i, A i) :
    (Algebra.trace R (∀ i, A i)) f = ∑ i, (Algebra.trace R (A i)) (f i) := by
  classical
  simp only [Algebra.trace_apply]
  rw [pi_lmul_decomp_aux f, map_sum]
  congr 1; ext i; exact trace_single_comp_aux i _

/-! ## Private scalar base-change lemmas (source-shaped) -/

/-- The global norm lands in the tensor product as the norm of a pure tensor. -/
private lemma norm_scalar_baseChange (v : HeightOneSpectrum (𝓞 K)) (α : L) :
    algebraMap K (v.adicCompletion K) (Algebra.norm K α) =
      @Algebra.norm (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) _ _
        Algebra.TensorProduct.rightAlgebra
        (α ⊗ₜ[K] (1 : v.adicCompletion K)) := by
  rw [Algebra.norm_apply K α,
    ← LinearMap.det_baseChange (Algebra.lmul K L α),
    Algebra.baseChange_lmul,
    ← Algebra.norm_apply (v.adicCompletion K)
      ((1 : v.adicCompletion K) ⊗ₜ[K] α)]
  have h : (Algebra.TensorProduct.commRight K (v.adicCompletion K) L)
      ((1 : v.adicCompletion K) ⊗ₜ[K] α) =
        (α ⊗ₜ[K] (1 : v.adicCompletion K)) := rfl
  rw [← h]
  exact (@Algebra.norm_eq_of_algEquiv (v.adicCompletion K)
    (v.adicCompletion K ⊗[K] L) (L ⊗[K] v.adicCompletion K) _ _ _
    _ Algebra.TensorProduct.rightAlgebra
    (Algebra.TensorProduct.commRight K (v.adicCompletion K) L)
    ((1 : v.adicCompletion K) ⊗ₜ[K] α)).symm

/-- The global trace lands in the tensor product as the trace of a pure tensor. -/
private lemma trace_scalar_baseChange (v : HeightOneSpectrum (𝓞 K)) (α : L) :
    algebraMap K (v.adicCompletion K) (Algebra.trace K L α) =
      @Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) _ _
        Algebra.TensorProduct.rightAlgebra
        (α ⊗ₜ[K] (1 : v.adicCompletion K)) := by
  rw [Algebra.trace_apply K α,
    ← LinearMap.trace_baseChange (Algebra.lmul K L α) (v.adicCompletion K),
    Algebra.baseChange_lmul,
    ← Algebra.trace_apply (v.adicCompletion K)
      ((1 : v.adicCompletion K) ⊗ₜ[K] α)]
  have h : (Algebra.TensorProduct.commRight K (v.adicCompletion K) L)
      ((1 : v.adicCompletion K) ⊗ₜ[K] α) =
        (α ⊗ₜ[K] (1 : v.adicCompletion K)) := rfl
  rw [← h]
  exact (@Algebra.trace_eq_of_algEquiv (v.adicCompletion K)
    (v.adicCompletion K ⊗[K] L) (L ⊗[K] v.adicCompletion K) _ _ _
    _ Algebra.TensorProduct.rightAlgebra
    (Algebra.TensorProduct.commRight K (v.adicCompletion K) L)
    ((1 : v.adicCompletion K) ⊗ₜ[K] α)).symm

/-! ## Private completion-factor finiteness -/

set_option linter.style.haveILetI false in
/-- Each completion factor is finite over the base completion, via the
surjective coordinate projection out of the finite tensor product. -/
private lemma finite_completion_factor (v : HeightOneSpectrum (𝓞 K))
    (w : v.placesOver L) :
    @Module.Finite (v.adicCompletion K) (w.val.adicCompletion L) _ _
      ((inferInstance : Algebra (v.adicCompletion K)
        (w.val.adicCompletion L))).toModule := by
  classical
  haveI : Module.Finite (v.adicCompletion K) (v.adicCompletion K ⊗[K] L) :=
    Module.Finite.base_change K _ L
  haveI : Module.Finite (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) :=
    Module.Finite.equiv
      (Algebra.TensorProduct.commRight K (v.adicCompletion K) L).toLinearEquiv
  haveI : Module.Finite (v.adicCompletion K)
      ((w' : v.placesOver L) → w'.val.adicCompletion L) :=
    Module.Finite.equiv
      (completionTensorProductRightAlgEquiv (K := K) (L := L) v).toLinearEquiv
  exact Module.Finite.of_surjective
    (LinearMap.proj (R := v.adicCompletion K)
      (φ := fun w' : v.placesOver L => w'.val.adicCompletion L) w)
    (LinearMap.proj_surjective w)

/-! ## Endpoint theorems -/

set_option linter.style.haveILetI false in
/-- **Global norm as a product of local norms.** Let $L/K$ be an extension of number fields, let
$v$ be a finite place of $K$, given as a height-one prime of the ring of integers $\mathcal{O}_K$,
and let $K_v$ be the completion of $K$ at $v$. For each of the finitely many finite places $w$ of
$L$ lying over $v$, regard the completion $L_w$ as a $K_v$-algebra through the continuous ring
homomorphism $K_v \to L_w$ extending $K \to L$. Then for every $\alpha \in L$, the image of the
norm $N_{L/K}(\alpha)$ in $K_v$ equals $\prod_{w \mid v} N_{L_w/K_v}(\alpha)$, where $\alpha$ is
viewed in $L_w$ and the product runs over the finite places $w$ of $L$ lying over $v$.

Source: Corollary 11.24, norm part. -/
theorem algebraMap_norm_eq_prod_adicCompletion
    (v : HeightOneSpectrum (𝓞 K)) [Fintype (v.placesOver L)] (α : L) :
    algebraMap K (v.adicCompletion K) (Algebra.norm K α) =
      ∏ w : v.placesOver L, Algebra.norm (v.adicCompletion K)
        (algebraMap L (w.val.adicCompletion L) α) := by
  classical
  haveI : ∀ w : v.placesOver L,
      @Module.Free (v.adicCompletion K) (w.val.adicCompletion L) _ _
        ((inferInstance : Algebra (v.adicCompletion K)
          (w.val.adicCompletion L))).toModule := fun w =>
    @Module.Free.of_divisionRing (v.adicCompletion K) (w.val.adicCompletion L)
      inferInstance inferInstance
      ((inferInstance : Algebra (v.adicCompletion K)
        (w.val.adicCompletion L))).toModule
  haveI : ∀ w : v.placesOver L,
      @Module.Finite (v.adicCompletion K) (w.val.adicCompletion L) _ _
        ((inferInstance : Algebra (v.adicCompletion K)
          (w.val.adicCompletion L))).toModule :=
    fun w => finite_completion_factor (K := K) (L := L) v w
  rw [norm_scalar_baseChange (K := K) (L := L) v α,
    ← Algebra.norm_eq_of_algEquiv
      (completionTensorProductRightAlgEquiv (K := K) (L := L) v)
      (α ⊗ₜ[K] (1 : v.adicCompletion K)),
    norm_pi_apply _]
  refine Finset.prod_congr rfl fun w _ => by
    congr 1
    exact completionTensorProductRightAlgEquiv_tmul_one (K := K) (L := L) v α w

set_option linter.style.haveILetI false in
/-- **Global trace as a sum of local traces.** Let $L/K$ be an extension of number fields, let
$v$ be a finite place of $K$, given as a height-one prime of the ring of integers $\mathcal{O}_K$,
and let $K_v$ be the completion of $K$ at $v$. For each of the finitely many finite places $w$ of
$L$ lying over $v$, regard the completion $L_w$ as a $K_v$-algebra through the continuous ring
homomorphism $K_v \to L_w$ extending $K \to L$. Then for every $\alpha \in L$, the image of the
trace $\operatorname{Tr}_{L/K}(\alpha)$ in $K_v$ equals
$\sum_{w \mid v} \operatorname{Tr}_{L_w/K_v}(\alpha)$, where $\alpha$ is viewed in $L_w$ and the
sum runs over the finite places $w$ of $L$ lying over $v$.

Source: Corollary 11.24, trace part. -/
theorem algebraMap_trace_eq_sum_adicCompletion
    (v : HeightOneSpectrum (𝓞 K)) [Fintype (v.placesOver L)] (α : L) :
    algebraMap K (v.adicCompletion K) (Algebra.trace K L α) =
      ∑ w : v.placesOver L, Algebra.trace (v.adicCompletion K)
        (w.val.adicCompletion L)
        (algebraMap L (w.val.adicCompletion L) α) := by
  classical
  haveI : ∀ w : v.placesOver L,
      @Module.Free (v.adicCompletion K) (w.val.adicCompletion L) _ _
        ((inferInstance : Algebra (v.adicCompletion K)
          (w.val.adicCompletion L))).toModule := fun w =>
    @Module.Free.of_divisionRing (v.adicCompletion K) (w.val.adicCompletion L)
      inferInstance inferInstance
      ((inferInstance : Algebra (v.adicCompletion K)
        (w.val.adicCompletion L))).toModule
  haveI : ∀ w : v.placesOver L,
      @Module.Finite (v.adicCompletion K) (w.val.adicCompletion L) _ _
        ((inferInstance : Algebra (v.adicCompletion K)
          (w.val.adicCompletion L))).toModule :=
    fun w => finite_completion_factor (K := K) (L := L) v w
  rw [trace_scalar_baseChange (K := K) (L := L) v α,
    ← Algebra.trace_eq_of_algEquiv
      (completionTensorProductRightAlgEquiv (K := K) (L := L) v)
      (α ⊗ₜ[K] (1 : v.adicCompletion K)),
    trace_pi_apply _]
  refine Finset.sum_congr rfl fun w _ => by
    congr 1
    exact completionTensorProductRightAlgEquiv_tmul_one (K := K) (L := L) v α w

end HeightOneSpectrum

end IsDedekindDomain
