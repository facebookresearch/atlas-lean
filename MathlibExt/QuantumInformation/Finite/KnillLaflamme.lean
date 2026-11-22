/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Correctable quantum codes and the Knill–Laflamme conditions

A quantum code is a subspace `C` of a finite-dimensional Hilbert space, given here by the
orthogonal projector `P` onto it. A family of error operators `A a` is correctable on the code
when some recovery operation, a quantum channel with Kraus operators `R r`
(`∑ r, (R r)ᴴ * R r = 1`), undoes every error on every code state up to a scalar:
`R r * A a * P = λ_{r a} • P` (Knill and Laflamme 1997, Section 3.1 and Theorem 3.1). Knill
and Laflamme's Theorem 3.2 characterises correctability without reference to the recovery:
`A` is correctable on `C` if and only if `P * (A a)ᴴ * A b * P` is a scalar multiple of `P`
for all `a, b`; in an orthonormal basis `|i_L⟩` of `C` these are their conditions
`⟨i_L| A_a† A_b |i_L⟩ = ⟨j_L| A_a† A_b |j_L⟩` and `⟨i_L| A_a† A_b |j_L⟩ = 0` for `i ≠ j`.

This file proves both halves of the Knill–Laflamme conditions. Necessity is
`knillLaflamme_of_isCorrectable`. Sufficiency, `isCorrectable_of_knillLaflamme`, builds the
recovery channel of Knill and Laflamme (proof of Theorem 3.2) and of Preskill's notes (equations
(7.28)–(7.32)). The two halves are combined in `isCorrectable_iff_knillLaflamme`.
`IsCorrectable.of_forall_mem_span` records that correctable families are linearly closed
(Knill and Laflamme, Theorem 3.1).

## Source

E. Knill and R. Laflamme, *Theory of quantum error-correcting codes*, Phys. Rev. A 55 (1997),
900–911 (arXiv:quant-ph/9604034), Section 3.1, Theorems 3.1 and 3.2.

J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7
(Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.2,
equations (7.19)–(7.32).
-/

@[expose] public section

open scoped BigOperators Matrix
open Matrix

namespace MathlibExt.QuantumInformation.Finite.KnillLaflamme

variable {n ι : Type*} [Fintype n] [DecidableEq n]

/-- **Correctable errors on a quantum code.** For the projector `P` onto a code and a family of
error operators `A a`, the errors are correctable on the code if there are finitely many
matrices `R r` with `∑ r, (R r)ᴴ * R r = 1` (the Kraus operators of a recovery channel) and
scalars with `R r * A a * P = λ_{r a} • P` for all `r` and `a`: after the error `A a` and the
recovery, every code state is restored up to a scalar. This is Knill and Laflamme's
`A`-correcting code (E. Knill and R. Laflamme, Phys. Rev. A 55 (1997), Section 3.1, with the
reformulation of Theorem 3.1). -/
def IsCorrectable (P : Matrix n n ℂ) (A : ι → Matrix n n ℂ) : Prop :=
  ∃ (N : ℕ) (R : Fin N → Matrix n n ℂ), ∑ r, (R r)ᴴ * R r = 1 ∧
    ∀ r a, ∃ c : ℂ, R r * A a * P = c • P

/-- **Necessity of the Knill–Laflamme conditions.** Let `P` be an orthogonal projector
(`Pᴴ = P`, `P * P = P`). If the errors `A a` are correctable on the code `range P`, then for all
`a` and `b` the compression `P * (A a)ᴴ * A b * P` is a scalar multiple of `P`. This is the
"only if" half of Theorem 3.2 of E. Knill and R. Laflamme, Phys. Rev. A 55 (1997), in projector
form. Proof: insert `1 = ∑ r, (R r)ᴴ * R r` between `(A a)ᴴ` and `A b`. -/
theorem knillLaflamme_of_isCorrectable {P : Matrix n n ℂ} (hP : Pᴴ = P) (hPP : P * P = P)
    {A : ι → Matrix n n ℂ} (h : IsCorrectable P A) (a b : ι) :
    ∃ c : ℂ, P * (A a)ᴴ * A b * P = c • P := by
  obtain ⟨N, R, hR, hRA⟩ := h
  choose f hf using hRA
  refine ⟨∑ r, star (f r a) * f r b, ?_⟩
  have key : ∀ r, (R r * A a * P)ᴴ * (R r * A b * P) =
      P * (A a)ᴴ * ((R r)ᴴ * R r) * A b * P := by
    intro r
    simp only [conjTranspose_mul, hP, Matrix.mul_assoc]
  calc P * (A a)ᴴ * A b * P = P * (A a)ᴴ * (∑ r, (R r)ᴴ * R r) * A b * P := by
        rw [hR, Matrix.mul_one]
    _ = ∑ r, P * (A a)ᴴ * ((R r)ᴴ * R r) * A b * P := by
        rw [Matrix.mul_sum, Finset.sum_mul, Finset.sum_mul]
    _ = ∑ r, (R r * A a * P)ᴴ * (R r * A b * P) := by
        simp only [key]
    _ = ∑ r, (star (f r a) * f r b) • P := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [hf r a, hf r b, conjTranspose_smul, hP, Matrix.smul_mul, Matrix.mul_smul, hPP,
          smul_smul]
    _ = (∑ r, star (f r a) * f r b) • P := Finset.sum_smul.symm

/-- **Correctable errors form a linear space.** If the errors `A a` are correctable on the code
with projector `P`, then so is every family `B b` of linear combinations of them, with the same
recovery channel (E. Knill and R. Laflamme, Phys. Rev. A 55 (1997), Theorem 3.1: "The family
`A(C, R)` is linearly closed"). This is why correcting a basis of errors, such as the Pauli
operators of weight at most `t`, corrects every error they span (J. Preskill, Ph219 lecture
notes, Chapter 7, Section 7.2). -/
theorem IsCorrectable.of_forall_mem_span {P : Matrix n n ℂ} {A : ι → Matrix n n ℂ}
    (h : IsCorrectable P A) {κ : Type*} {B : κ → Matrix n n ℂ}
    (hB : ∀ b, B b ∈ Submodule.span ℂ (Set.range A)) : IsCorrectable P B := by
  obtain ⟨N, R, hR, hRA⟩ := h
  refine ⟨N, R, hR, fun r b => ?_⟩
  suffices key : ∀ X ∈ Submodule.span ℂ (Set.range A), ∃ c : ℂ, R r * X * P = c • P from
    key _ (hB b)
  intro X hX
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact hRA r a
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨c + d, by rw [Matrix.mul_add, Matrix.add_mul, hc, hd, add_smul]⟩
  | smul e x _ hx =>
    obtain ⟨c, hc⟩ := hx
    exact ⟨e * c, by rw [Matrix.mul_smul, Matrix.smul_mul, hc, smul_smul]⟩

end MathlibExt.QuantumInformation.Finite.KnillLaflamme

namespace MathlibExt.QuantumInformation.Finite.KnillLaflamme

open scoped InnerProductSpace

variable {n ι : Type*} [Fintype n] [DecidableEq n]

/- Vectorisation of a matrix: `Matrix n n ℂ` with the Hilbert–Schmidt inner product
`⟪X, Y⟫ = trace (Xᴴ * Y)` is the Euclidean space on `n × n`. -/
private noncomputable def vecL : Matrix n n ℂ ≃ₗ[ℂ] EuclideanSpace ℂ (n × n) :=
  (LinearEquiv.curry ℂ ℂ n n).symm.trans (WithLp.linearEquiv 2 ℂ (n × n → ℂ)).symm

omit [Fintype n] [DecidableEq n] in
private theorem vecL_apply (X : Matrix n n ℂ) (p : n × n) : (vecL X).ofLp p = X p.1 p.2 := rfl

omit [DecidableEq n] in
private theorem inner_vecL (X Y : Matrix n n ℂ) : ⟪vecL X, vecL Y⟫_ℂ = trace (Xᴴ * Y) := by
  simp only [PiLp.inner_apply, vecL_apply, trace, diag, mul_apply, conjTranspose_apply,
    Fintype.sum_prod_type, RCLike.inner_apply]
  rw [Finset.sum_comm]
  simp [mul_comm]

/- The span `W` of the corrupted code spaces `A a * P`: its elements are fixed by right
multiplication by `P`, and the Knill–Laflamme conditions extend to it bilinearly. -/
omit [DecidableEq n] in
private theorem mul_proj_of_mem_span {P : Matrix n n ℂ} (hPP : P * P = P)
    {A : ι → Matrix n n ℂ} {X : Matrix n n ℂ}
    (hX : X ∈ Submodule.span ℂ (Set.range fun a => A a * P)) : X * P = X := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [Matrix.mul_assoc, hPP]
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_mul, hx, hy]
  | smul c x _ hx => rw [Matrix.smul_mul, hx]

omit [DecidableEq n] in
private theorem knillLaflamme_span {P : Matrix n n ℂ} (hP : Pᴴ = P) (hPP : P * P = P)
    {A : ι → Matrix n n ℂ} (h : ∀ a b, ∃ c : ℂ, P * (A a)ᴴ * A b * P = c • P)
    {X Y : Matrix n n ℂ} (hX : X ∈ Submodule.span ℂ (Set.range fun a => A a * P))
    (hY : Y ∈ Submodule.span ℂ (Set.range fun a => A a * P)) :
    ∃ c : ℂ, P * Xᴴ * Y * P = c • P := by
  induction hX using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    induction hY using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      obtain ⟨c, hc⟩ := h a b
      refine ⟨c, ?_⟩
      calc P * (A a * P)ᴴ * (A b * P) * P = P * (P * (A a)ᴴ * A b * P) * P := by
            simp only [conjTranspose_mul, hP, Matrix.mul_assoc]
        _ = c • P := by rw [hc, Matrix.mul_smul, Matrix.smul_mul, hPP, hPP]
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨c, hc⟩ := hy
      obtain ⟨d, hd⟩ := hz
      exact ⟨c + d, by rw [Matrix.mul_add, Matrix.add_mul, hc, hd, add_smul]⟩
    | smul e y _ hy =>
      obtain ⟨c, hc⟩ := hy
      exact ⟨e * c, by rw [Matrix.mul_smul, Matrix.smul_mul, hc, smul_smul]⟩
  | zero => exact ⟨0, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hz
    exact ⟨c + d, by rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, hc,
      hd, add_smul]⟩
  | smul e x _ hx =>
    obtain ⟨c, hc⟩ := hx
    exact ⟨star e * c, by rw [conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_mul, hc, smul_smul]⟩

/- The recovery channel from a family `F` with `(F i)ᴴ * F j = δ_{ij} P` whose span contains
every `A a * P`: Kraus operators `1 - ∑ F i * (F i)ᴴ` and `P * (F i)ᴴ` (Preskill, eq. (7.29),
with the complementary projection added after eq. (7.32)). -/
private theorem isCorrectable_of_frame {P : Matrix n n ℂ} (hP : Pᴴ = P) (hPP : P * P = P)
    {A : ι → Matrix n n ℂ} {m : ℕ} (F : Fin m → Matrix n n ℂ)
    (hFP : ∀ i, F i * P = F i) (hFF : ∀ i j, (F i)ᴴ * F j = if i = j then P else 0)
    (hexp : ∀ a, ∃ β : Fin m → ℂ, A a * P = ∑ j, β j • F j) :
    IsCorrectable P A := by
  classical
  have hFP' : ∀ i, P * (F i)ᴴ = (F i)ᴴ := fun i => by
    rw [← hP, ← conjTranspose_mul, hFP]
  set Q : Matrix n n ℂ := ∑ i, F i * (F i)ᴴ with hQ
  have hQX : ∀ β : Fin m → ℂ, Q * ∑ j, β j • F j = ∑ j, β j • F j := by
    intro β
    simp only [hQ, Finset.sum_mul, Finset.mul_sum, Matrix.mul_smul, Matrix.mul_assoc, hFF,
      mul_ite, Matrix.mul_zero, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, hFP]
  have hQQ : Q * Q = Q := by
    rw [hQ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Matrix.mul_assoc]
    congr 1
    simpa using hQX (Pi.single i 1)
  have hQh : Qᴴ = Q := by
    simp [hQ, conjTranspose_sum, conjTranspose_mul]
  refine ⟨m + 1, Fin.cons (1 - Q) fun i => P * (F i)ᴴ, ?_, ?_⟩
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have hterm : ∀ i, (P * (F i)ᴴ)ᴴ * (P * (F i)ᴴ) = F i * (F i)ᴴ := fun i => by
      rw [hFP' i, conjTranspose_conjTranspose]
    simp only [hterm, ← hQ, conjTranspose_sub, conjTranspose_one, hQh, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hQQ]
    abel
  · intro r a
    obtain ⟨β, hβ⟩ := hexp a
    refine Fin.cases ?_ (fun i => ?_) r
    · refine ⟨0, ?_⟩
      rw [Fin.cons_zero, zero_smul, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hβ,
        hQX, sub_self]
    · refine ⟨β i, ?_⟩
      rw [Fin.cons_succ, Matrix.mul_assoc, hβ, Matrix.mul_assoc, Finset.mul_sum]
      simp only [Matrix.mul_smul, hFF, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ,
        ite_true, hPP]

/-- **Sufficiency of the Knill–Laflamme conditions.** Let `P` be an orthogonal projector on a
finite-dimensional complex Hilbert space (`Pᴴ = P`, `P * P = P`) and let `A a` be error
operators. If for all `a` and `b` the compression `P * (A a)ᴴ * A b * P` is a scalar multiple
of `P`, then the errors are correctable on the code `range P`: some recovery channel restores
every code state after every error, up to a scalar (`IsCorrectable`). This is the "if" half of
Theorem 3.2 of E. Knill and R. Laflamme, Phys. Rev. A 55 (1997), stated with the projector `P`
in place of an orthonormal basis of the code. -/
theorem isCorrectable_of_knillLaflamme {n ι : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℂ) (hP : Pᴴ = P) (hPP : P * P = P) (A : ι → Matrix n n ℂ)
    (h : ∀ a b, ∃ c : ℂ, P * (A a)ᴴ * A b * P = c • P) :
    IsCorrectable P A := by
  classical
  by_cases hP0 : P = 0
  · subst hP0
    exact ⟨1, fun _ => 1, by simp, fun _ _ => ⟨0, by simp⟩⟩
  set W : Submodule ℂ (Matrix n n ℂ) := Submodule.span ℂ (Set.range fun a => A a * P)
  -- the normalisation `trace P = t ^ 2`, with `t` the Hilbert–Schmidt norm of `P`
  set t : ℂ := (‖vecL P‖ : ℂ) with ht
  have htrP : trace P = t ^ 2 := by
    have h1 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (vecL P)
    rw [inner_vecL, hP, hPP] at h1
    exact h1
  have ht0 : t ≠ 0 := by
    rw [ht, Complex.ofReal_ne_zero, norm_ne_zero_iff]
    exact fun h0 => hP0 (vecL.injective (by rw [h0, map_zero]))
  -- an orthonormal basis `b` of `W` for the Hilbert–Schmidt inner product, rescaled by `t`
  set W' : Submodule ℂ (EuclideanSpace ℂ (n × n)) := W.map (vecL (n := n)).toLinearMap
  set b := stdOrthonormalBasis ℂ W'
  set F : Fin (Module.finrank ℂ W') → Matrix n n ℂ :=
    fun i => t • vecL.symm (b i : EuclideanSpace ℂ (n × n))
  have hFW : ∀ i, F i ∈ W := by
    intro i
    refine W.smul_mem t ?_
    obtain ⟨X, hX, hXe⟩ := Submodule.mem_map.1 (b i).2
    rw [← hXe]
    simpa using hX
  have hFP : ∀ i, F i * P = F i := fun i => mul_proj_of_mem_span hPP (hFW i)
  have htr : ∀ i j, trace ((F i)ᴴ * F j) = if i = j then t ^ 2 else 0 := by
    intro i j
    have hb : ⟪(b i : EuclideanSpace ℂ (n × n)), (b j : EuclideanSpace ℂ (n × n))⟫_ℂ =
        if i = j then 1 else 0 := by
      rw [← Submodule.coe_inner]
      exact orthonormal_iff_ite.1 b.orthonormal i j
    have hstar : star t = t := by rw [ht]; exact Complex.conj_ofReal _
    simp only [F, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, trace_smul, smul_smul,
      ← inner_vecL, LinearEquiv.apply_symm_apply, hb, hstar]
    split_ifs <;> simp [sq]
  -- the Knill–Laflamme constants of the `F i` form the identity matrix
  have hFF : ∀ i j, (F i)ᴴ * F j = if i = j then P else 0 := by
    intro i j
    obtain ⟨c, hc⟩ := knillLaflamme_span hP hPP h (hFW i) (hFW j)
    have hc' : (F i)ᴴ * F j = c • P := by
      rw [← hc, ← hP, ← conjTranspose_mul, hFP i, hP, Matrix.mul_assoc, hFP j]
    have hcv : c * t ^ 2 = if i = j then t ^ 2 else 0 := by
      rw [← htr, hc', trace_smul, htrP, smul_eq_mul]
    have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
    rw [hc']
    split_ifs at hcv ⊢
    · rw [(mul_eq_right₀ ht2).1 hcv, one_smul]
    · rw [(mul_eq_zero.1 hcv).resolve_right ht2, zero_smul]
  -- every `A a * P` expands in the `F i`
  refine isCorrectable_of_frame hP hPP F hFP hFF fun a => ?_
  have hx : vecL (A a * P) ∈ W' := Submodule.mem_map_of_mem (Submodule.subset_span ⟨a, rfl⟩)
  refine ⟨fun j => t⁻¹ * b.repr ⟨vecL (A a * P), hx⟩ j, ?_⟩
  have hs' := congrArg (fun v : W' => vecL.symm (v : EuclideanSpace ℂ (n × n)))
    (b.sum_repr ⟨vecL (A a * P), hx⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
    LinearEquiv.symm_apply_apply] at hs'
  refine hs'.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
  simp only [F, smul_smul]
  rw [mul_comm _ t, ← mul_assoc, mul_inv_cancel₀ ht0, one_mul]

end MathlibExt.QuantumInformation.Finite.KnillLaflamme

namespace MathlibExt.QuantumInformation.Finite.KnillLaflamme

/-- **The Knill–Laflamme conditions.** Let `P` be an orthogonal projector on a
finite-dimensional complex Hilbert space (`Pᴴ = P`, `P * P = P`). A family of error operators
`A a` is correctable on the code `range P` if and only if for all `a` and `b` the compression
`P * (A a)ᴴ * A b * P` is a scalar multiple of `P` (E. Knill and R. Laflamme, Phys. Rev. A 55
(1997), Theorem 3.2, in projector form; J. Preskill, Ph219 lecture notes, Chapter 7,
equation (7.19)). -/
theorem isCorrectable_iff_knillLaflamme {n ι : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℂ} (hP : Pᴴ = P) (hPP : P * P = P) {A : ι → Matrix n n ℂ} :
    IsCorrectable P A ↔ ∀ a b, ∃ c : ℂ, P * (A a)ᴴ * A b * P = c • P :=
  ⟨fun h => knillLaflamme_of_isCorrectable hP hPP h,
    isCorrectable_of_knillLaflamme P hP hPP A⟩

end MathlibExt.QuantumInformation.Finite.KnillLaflamme
