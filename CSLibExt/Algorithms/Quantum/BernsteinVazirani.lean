/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Fourier sampling: the Deutsch–Jozsa and Bernstein–Vazirani algorithms

The `n`-qubit Hadamard transform is the unitary change of basis from the computational basis
of `ℂ^(Z₂ⁿ)` to the parity basis `x ↦ (-1)^(s·x) / 2^(n/2)` (Bernstein and Vazirani,
"Quantum complexity theory", SIAM J. Comput. 26 (1997), Section 8.4). Fourier sampling with
respect to a Boolean function `f` prepares `H Oₓ H |0…0⟩`, where `O_f` is the phase oracle
`|x⟩ ↦ (-1)^(f x) |x⟩`; the amplitude of `|t⟩` is `2⁻ⁿ ∑ₓ (-1)^(f x + t·x)`.

* If `f x = s·x + b`, the final state is `(-1)^b |s⟩`: one query recovers `s` with certainty
  (the Bernstein–Vazirani parity problem).
* If `f` is constant, the final state is `±|0…0⟩`; if `f` is balanced, `|0…0⟩` has amplitude
  `0` (the Deutsch–Jozsa problem, in the one-query form of Cleve, Ekert, Macchiavello and
  Mosca).

The phase oracle is what a reversible oracle `|x⟩|b⟩ ↦ |x⟩|b + f x⟩` does to a target qubit
prepared in `|0⟩ - |1⟩` (`phase_kickback`). On the classical side, fewer than `n` evaluations
of `x ↦ s·x` never determine `s` (`exists_ne_zero_forall_bitDot_eq_zero`).

## Sources

* E. Bernstein and U. Vazirani, *Quantum complexity theory*, SIAM J. Comput. 26 (1997),
  1411–1473; author-hosted version dated September 8, 1997, Section 8.4 (Fourier sampling,
  Theorems 8.4.1 and 8.4.2, and the parity problem that follows them).
* R. Cleve, A. Ekert, C. Macchiavello and M. Mosca, *Quantum algorithms revisited*,
  Proc. R. Soc. Lond. A 454 (1998), 339–354; arXiv:quant-ph/9708016v1, Section 3,
  equations (3.1)–(3.9).
-/

@[expose] public section

open Matrix Finset

namespace Cslib.BernsteinVazirani

variable {n : ℕ}

/-- **Inner product of bit strings modulo two.** For `s x : Fin n → ZMod 2`,
`s·x = ∑ᵢ sᵢ xᵢ` in `ZMod 2` (Cleve, Ekert, Macchiavello and Mosca, arXiv:quant-ph/9708016,
equation (3.2)). -/
def bitDot (s x : Fin n → ZMod 2) : ZMod 2 := ∑ i, s i * x i

/-- **Sign of a bit.** `(-1)^b` as a complex number, for `b : ZMod 2`. -/
def signOfBit (b : ZMod 2) : ℂ := if b = 0 then 1 else -1

theorem add_eq_zero_iff_eq (s t : Fin n → ZMod 2) : s + t = 0 ↔ s = t := by
  constructor
  · intro h
    funext i
    have := congrFun h i
    simp only [Pi.add_apply, Pi.zero_apply] at this
    rw [eq_neg_of_add_eq_zero_left this, ZMod.neg_eq_self_mod_two]
  · rintro rfl
    funext i
    simp [← two_mul, show (2 : ZMod 2) = 0 from rfl]

theorem bitDot_comm (s x : Fin n → ZMod 2) : bitDot s x = bitDot x s := by
  simp only [bitDot, mul_comm]

@[simp]
theorem bitDot_zero_left (x : Fin n → ZMod 2) : bitDot 0 x = 0 := by
  simp [bitDot]

@[simp]
theorem bitDot_zero_right (s : Fin n → ZMod 2) : bitDot s 0 = 0 := by
  simp [bitDot]

theorem bitDot_add_left (s t x : Fin n → ZMod 2) : bitDot (s + t) x = bitDot s x + bitDot t x := by
  simp [bitDot, add_mul, sum_add_distrib]

theorem bitDot_add_right (s x y : Fin n → ZMod 2) : bitDot s (x + y) = bitDot s x + bitDot s y := by
  simp [bitDot, mul_add, sum_add_distrib]

theorem bitDot_single (s : Fin n → ZMod 2) (i : Fin n) : bitDot s (Pi.single i 1) = s i := by
  simp [bitDot, Pi.single_apply]

private theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

private theorem zmod_two_one_ne_zero : (1 : ZMod 2) ≠ 0 := by decide

private theorem zmod_two_one_add_one : (1 : ZMod 2) + 1 = 0 := rfl

@[simp]
theorem signOfBit_zero : signOfBit 0 = 1 := by simp [signOfBit]

@[simp]
theorem signOfBit_one : signOfBit 1 = -1 := by simp [signOfBit]

theorem signOfBit_add (a b : ZMod 2) : signOfBit (a + b) = signOfBit a * signOfBit b := by
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl <;>
    simp [zmod_two_one_add_one]

theorem signOfBit_mul_self (a : ZMod 2) : signOfBit a * signOfBit a = 1 := by
  rcases zmod_two_cases a with rfl | rfl <;> simp

theorem star_signOfBit (a : ZMod 2) : star (signOfBit a) = signOfBit a := by
  rcases zmod_two_cases a with rfl | rfl <;> simp

/-- **Orthogonality of the parity characters.** For `u : Fin n → ZMod 2`,
`∑ₓ (-1)^(u·x)` is `2ⁿ` if `u = 0` and `0` otherwise (Bernstein and Vazirani, Section 8.4:
the parity functions form an orthonormal basis). -/
theorem sum_signOfBit_bitDot (u : Fin n → ZMod 2) :
    ∑ x, signOfBit (bitDot u x) = if u = 0 then (2 : ℂ) ^ n else 0 := by
  split_ifs with hu
  · subst hu
    simp [ZMod.card]
  · obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra h
      push Not at h
      exact hu (funext h)
    have hi1 : u i = 1 := (zmod_two_cases (u i)).resolve_left hi
    set S := ∑ x, signOfBit (bitDot u x) with hS
    have hflip : S = -S := by
      calc S = ∑ x, signOfBit (bitDot u (x + Pi.single i 1)) :=
            (Fintype.sum_equiv (Equiv.addRight (Pi.single i 1)) _ _ (fun _ => rfl)).symm
        _ = ∑ x, -signOfBit (bitDot u x) := by
            refine sum_congr rfl fun x _ => ?_
            rw [bitDot_add_right, bitDot_single, hi1, signOfBit_add, signOfBit_one, mul_neg_one]
        _ = -S := by rw [sum_neg_distrib]
    linear_combination hflip / 2

/-- **Normalisation of the Hadamard transform.** The scalar `2^(-n/2)`. -/
noncomputable def hadamardScale (n : ℕ) : ℂ := ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹

theorem hadamardScale_mul_self (n : ℕ) : hadamardScale n * hadamardScale n = ((2 : ℂ) ^ n)⁻¹ := by
  rw [hadamardScale, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  push_cast
  rfl

theorem star_hadamardScale (n : ℕ) : star (hadamardScale n) = hadamardScale n := by
  simp [hadamardScale]

/-- **The `n`-qubit Hadamard transform.** The matrix indexed by `Z₂ⁿ` with entry
`2^(-n/2) (-1)^(s·x)` in row `s`, column `x`; it maps `|x⟩` to
`2^(-n/2) ∑ₛ (-1)^(s·x) |s⟩` (Bernstein and Vazirani, Section 8.4, Theorem 8.4.1;
Cleve, Ekert, Macchiavello and Mosca, arXiv:quant-ph/9708016, equation (3.1), whose
display omits the normalisation). -/
noncomputable def hadamard (n : ℕ) : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  Matrix.of fun s x => hadamardScale n * signOfBit (bitDot s x)

theorem hadamard_apply (s x : Fin n → ZMod 2) :
    hadamard n s x = hadamardScale n * signOfBit (bitDot s x) := rfl

/-- **The Hadamard transform is symmetric.** -/
theorem hadamard_transpose (n : ℕ) : (hadamard n)ᵀ = hadamard n := by
  ext s x
  simp [hadamard_apply, bitDot_comm]

/-- **The Hadamard transform is self-adjoint.** Its entries are real. -/
theorem hadamard_conjTranspose (n : ℕ) : (hadamard n)ᴴ = hadamard n := by
  ext s x
  simp [hadamard_apply, star_hadamardScale, star_signOfBit, bitDot_comm]

/-- **The Hadamard transform is an involution.** `H H = 1`, by orthogonality of the parity
characters (Bernstein and Vazirani, Section 8.4). -/
theorem hadamard_mul_self (n : ℕ) : hadamard n * hadamard n = 1 := by
  ext s t
  have hst := add_eq_zero_iff_eq s t
  calc (hadamard n * hadamard n) s t
      = hadamardScale n * hadamardScale n * ∑ x, signOfBit (bitDot (s + t) x) := by
        simp only [Matrix.mul_apply, hadamard_apply, mul_sum]
        refine sum_congr rfl fun x _ => ?_
        rw [bitDot_add_left, signOfBit_add, bitDot_comm x t]
        ring
    _ = (1 : Matrix _ _ ℂ) s t := by
        rw [sum_signOfBit_bitDot, hadamardScale_mul_self, Matrix.one_apply]
        by_cases h : s = t
        · subst h
          simp [add_eq_zero_iff_eq]
        · simp only [mt hst.mp h, h, ↓reduceIte, mul_zero]

/-- **The Hadamard transform is unitary.** -/
theorem hadamard_mem_unitaryGroup (n : ℕ) :
    hadamard n ∈ Matrix.unitaryGroup (Fin n → ZMod 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, hadamard_conjTranspose,
    hadamard_mul_self]

/-- **Sylvester sign matrix.** The `±1` matrix indexed by `Z₂ⁿ` with entry `(-1)^(s·x)`; the
Hadamard transform is `2^(-n/2)` times it (`hadamard_eq_smul_sylvesterSignMatrix`). -/
def sylvesterSignMatrix (n : ℕ) : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  Matrix.of fun s x => signOfBit (bitDot s x)

theorem hadamard_eq_smul_sylvesterSignMatrix (n : ℕ) :
    hadamard n = hadamardScale n • sylvesterSignMatrix n := by
  ext s x
  simp [hadamard_apply, sylvesterSignMatrix]

/-- **The sign matrix is a Hadamard matrix.** `(-1)^(s·x)` is a Hadamard matrix of order `2ⁿ` in
the sense of Mathlib's `Matrix.IsHadamard`: its entries are `±1` and its rows are orthogonal,
by orthogonality of the parity characters (Bernstein and Vazirani, Section 8.4). -/
theorem isHadamard_sylvesterSignMatrix (n : ℕ) : (sylvesterSignMatrix n).IsHadamard := by
  have hmul : sylvesterSignMatrix n * (sylvesterSignMatrix n)ᴴ =
      (Fintype.card (Fin n → ZMod 2) : ℂ) • (1 : Matrix _ _ ℂ) := by
    ext s t
    have : (sylvesterSignMatrix n * (sylvesterSignMatrix n)ᴴ) s t =
        ∑ x, signOfBit (bitDot (s + t) x) := by
      simp only [Matrix.mul_apply, conjTranspose_apply, sylvesterSignMatrix, of_apply,
        star_signOfBit]
      refine sum_congr rfl fun x _ => ?_
      rw [bitDot_add_left, signOfBit_add]
    rw [this, sum_signOfBit_bitDot]
    simp only [add_eq_zero_iff_eq, Matrix.smul_apply, Matrix.one_apply, Fintype.card_fun,
      ZMod.card, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    split_ifs <;> simp
  refine ⟨fun s x => ?_, hmul, ?_⟩
  · rcases zmod_two_cases (bitDot s x) with h | h
    · simp [sylvesterSignMatrix, h]
    · simp only [sylvesterSignMatrix, of_apply, h, signOfBit_one]
      rw [Unitary.mem_iff]
      simp
  · have hT : (sylvesterSignMatrix n)ᴴ = sylvesterSignMatrix n := by
      ext s x
      simp [sylvesterSignMatrix, star_signOfBit, bitDot_comm]
    rw [hT] at hmul ⊢
    exact hmul

/-- **Phase oracle.** For `f : Z₂ⁿ → Z₂`, the diagonal unitary `|x⟩ ↦ (-1)^(f x) |x⟩`
(Cleve, Ekert, Macchiavello and Mosca, arXiv:quant-ph/9708016, equation (3.5)). -/
noncomputable def phaseOracle (f : (Fin n → ZMod 2) → ZMod 2) :
    Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℂ :=
  Matrix.diagonal fun x => signOfBit (f x)

/-- **Phase kickback.** The reversible oracle `|x⟩|b⟩ ↦ |x⟩|b + f x⟩`, applied to a state whose
target qubit is `|0⟩ - |1⟩` (amplitude `a x · (-1)^b` at `(x, b)`), multiplies the amplitude at
`(x, b)` by `(-1)^(f x)` (Cleve, Ekert, Macchiavello and Mosca, arXiv:quant-ph/9708016,
equations (3.3)–(3.5)). Here a state is a function on `Z₂ⁿ × Z₂` and the oracle acts by
`v ↦ ((x, b) ↦ v (x, b + f x))`. -/
theorem phase_kickback (f : (Fin n → ZMod 2) → ZMod 2) (a : (Fin n → ZMod 2) → ℂ)
    (x : Fin n → ZMod 2) (b : ZMod 2) :
    (fun p : (Fin n → ZMod 2) × ZMod 2 => a p.1 * signOfBit p.2) (x, b + f x) =
      signOfBit (f x) * (a x * signOfBit b) := by
  simp only [signOfBit_add]
  ring

/-- **Fourier sampling state.** For `f : Z₂ⁿ → Z₂`, the state `H O_f H |0…0⟩`: one query to
the phase oracle between two Hadamard transforms (Bernstein and Vazirani, Section 8.4,
Theorem 8.4.2; Cleve, Ekert, Macchiavello and Mosca, arXiv:quant-ph/9708016, Figure 4). -/
noncomputable def fourierSample (f : (Fin n → ZMod 2) → ZMod 2) : (Fin n → ZMod 2) → ℂ :=
  hadamard n *ᵥ (phaseOracle f *ᵥ (hadamard n *ᵥ Pi.single 0 1))

/-- **Amplitudes of Fourier sampling.** The amplitude of `|t⟩` in `H O_f H |0…0⟩` is
`2⁻ⁿ ∑ₓ (-1)^(f x + t·x)` (Cleve, Ekert, Macchiavello and Mosca, arXiv:quant-ph/9708016,
equation (3.6), with the normalisation restored; Bernstein and Vazirani, Theorem 8.4.2). -/
theorem fourierSample_apply (f : (Fin n → ZMod 2) → ZMod 2) (t : Fin n → ZMod 2) :
    fourierSample f t = ((2 : ℂ) ^ n)⁻¹ * ∑ x, signOfBit (f x + bitDot t x) := by
  have h0 : hadamard n *ᵥ Pi.single 0 1 = fun _ => hadamardScale n := by
    funext s
    simp [hadamard_apply]
  have h1 : phaseOracle f *ᵥ (fun _ => hadamardScale n) =
      fun x => signOfBit (f x) * hadamardScale n := by
    funext x
    simp [phaseOracle, mulVec_diagonal]
  rw [fourierSample, h0, h1, ← hadamardScale_mul_self, mul_sum]
  simp only [mulVec, dotProduct, hadamard_apply]
  refine sum_congr rfl fun x _ => ?_
  rw [signOfBit_add, bitDot_comm t x]
  ring

/-- **Bernstein–Vazirani algorithm.** If `f x = s·x + b` for all `x`, then one query of
Fourier sampling produces the state `(-1)^b |s⟩` (Cleve, Ekert, Macchiavello and Mosca,
arXiv:quant-ph/9708016, equations (3.7)–(3.9); Bernstein and Vazirani, Section 8.4, the
parity problem, where `b = 0`). -/
theorem fourierSample_of_affine (s : Fin n → ZMod 2) (b : ZMod 2)
    (f : (Fin n → ZMod 2) → ZMod 2) (hf : ∀ x, f x = bitDot s x + b) :
    fourierSample f = signOfBit b • Pi.single s 1 := by
  funext t
  rw [fourierSample_apply]
  have : ∀ x, signOfBit (f x + bitDot t x) = signOfBit b * signOfBit (bitDot (s + t) x) :=
      fun x => by
    rw [hf, bitDot_add_left, signOfBit_add, signOfBit_add, signOfBit_add]
    ring
  simp only [this, ← mul_sum, sum_signOfBit_bitDot]
  have hst : (s + t = 0) ↔ t = s := (add_eq_zero_iff_eq s t).trans eq_comm
  by_cases h : t = s
  · subst h
    simp [add_eq_zero_iff_eq]
    field_simp
  · simp only [mt hst.mp h, ↓reduceIte, mul_zero]
    simp [h]

/-- **The Bernstein–Vazirani algorithm outputs `s` with certainty.** If `f x = s·x + b`, then
measuring `H O_f H |0…0⟩` in the computational basis gives `t` with probability
`|amplitude|² = 1` if `t = s` and `0` otherwise (Bernstein and Vazirani, Section 8.4; Cleve,
Ekert, Macchiavello and Mosca, arXiv:quant-ph/9708016, equation (3.9)). -/
theorem normSq_fourierSample_of_affine (s : Fin n → ZMod 2) (b : ZMod 2)
    (f : (Fin n → ZMod 2) → ZMod 2) (hf : ∀ x, f x = bitDot s x + b) (t : Fin n → ZMod 2) :
    Complex.normSq (fourierSample f t) = if t = s then 1 else 0 := by
  rw [fourierSample_of_affine s b f hf]
  by_cases h : t = s
  · subst h
    rcases zmod_two_cases b with rfl | rfl <;> simp
  · simp [h]

/-- **Balanced Boolean function.** `f : Z₂ⁿ → Z₂` takes the values `0` and `1` equally often
(Cleve, Ekert, Macchiavello and Mosca, arXiv:quant-ph/9708016, Section 3). -/
def IsBalanced (f : (Fin n → ZMod 2) → ZMod 2) : Prop :=
  (univ.filter fun x => f x = 0).card = (univ.filter fun x => f x = 1).card

theorem sum_signOfBit_eq_zero_of_isBalanced {f : (Fin n → ZMod 2) → ZMod 2} (hf : IsBalanced f) :
    ∑ x, signOfBit (f x) = 0 := by
  have h1 : (univ.filter fun x => ¬ f x = 0) = univ.filter fun x => f x = 1 := by
    ext x
    simp only [mem_filter, mem_univ, true_and]
    rcases zmod_two_cases (f x) with h | h <;> simp [h]
  unfold IsBalanced at hf
  simp only [signOfBit, sum_ite, sum_const, h1, ← hf]
  simp

/-- **Deutsch–Jozsa algorithm, constant case.** If `f` is constant, measuring
`H O_f H |0…0⟩` gives `0…0` with probability `1` (Cleve, Ekert, Macchiavello and Mosca,
arXiv:quant-ph/9708016, Section 3, after equation (3.6)). -/
theorem normSq_fourierSample_zero_of_const (b : ZMod 2) :
    Complex.normSq (fourierSample (n := n) (fun _ => b) 0) = 1 := by
  simpa using normSq_fourierSample_of_affine (n := n) 0 b (fun _ => b) (by simp) 0

/-- **Deutsch–Jozsa algorithm, balanced case.** If `f` is balanced, the amplitude of `|0…0⟩` in
`H O_f H |0…0⟩` is `0`, so measuring never gives `0…0` (Cleve, Ekert, Macchiavello and Mosca,
arXiv:quant-ph/9708016, Section 3, after equation (3.6)). Together with the constant case,
one query distinguishes constant from balanced functions with certainty. -/
theorem fourierSample_zero_of_isBalanced {f : (Fin n → ZMod 2) → ZMod 2}
    (hf : IsBalanced f) : fourierSample f 0 = 0 := by
  rw [fourierSample_apply]
  simp [sum_signOfBit_eq_zero_of_isBalanced hf]

/-- **Classical evaluations: fewer than `n` never determine `s`.** For every set `Q` of fewer
than `n` query points in `Z₂ⁿ` there is `u ≠ 0` with `u·x = 0` for all `x ∈ Q`, so the
functions `x ↦ s·x` and `x ↦ (s + u)·x` agree on `Q`. This is the counting fact behind the
remark that a classical algorithm needs `n` evaluations to find `s` (Bernstein and Vazirani,
Section 8.4, after Theorem 8.4.2; Cleve, Ekert, Macchiavello and Mosca, arXiv:quant-ph/9708016,
after equation (3.7)). -/
theorem exists_ne_zero_forall_bitDot_eq_zero (Q : Finset (Fin n → ZMod 2)) (hQ : Q.card < n) :
    ∃ u : Fin n → ZMod 2, u ≠ 0 ∧ ∀ x ∈ Q, bitDot u x = 0 := by
  let M : Matrix Q (Fin n) (ZMod 2) := fun x i => (x : Fin n → ZMod 2) i
  have hker : LinearMap.ker (Matrix.mulVecLin M) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (K := ZMod 2) (by simpa using hQ)
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨u, hu0, fun x hx => ?_⟩
  have := congrFun (LinearMap.mem_ker.mp hu) ⟨x, hx⟩
  change (M *ᵥ u) ⟨x, hx⟩ = 0 at this
  simpa [M, mulVec, dotProduct, bitDot, mul_comm] using this

end Cslib.BernsteinVazirani
