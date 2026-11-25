/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing

/-!
# Nilpotency class of nilpotent Camina-type groups (Kourovka Notebook Problem 17.47)

Kourovka Notebook, Problem 17.47 (S. H. Ghate, A. S. Muktibodh): let `G` be a nilpotent group in
which every coset `x[G, G]` for `x ∉ [G, G]` coincides with the conjugacy class `x^G`. Is there a
bound for the nilpotency class of `G`? (If `G` is finite, its class is at most 3 (R. Dark, C.
Scoppola).)

The main result, `nilpotentCaminaClassBounded_refuted`, answers the question in the negative: for
every `c` there is a nilpotent group of class greater than `c` in which `x^G = x[G, G]` for every
`x ∉ [G, G]`.

## Construction

The proof does not follow Ionin and Semidetnov, who use a field of characteristic zero with a
surjective derivation. Let `K` be the algebraic closure of `ZMod 2` and `σ` its Frobenius map
`z ↦ z ^ 2`. Fix `n ≥ 1`. The upper triangular `(n + 1) × (n + 1)` matrices `M` over `K` with
`M (i + 1) (j + 1) = σ (M i j)` form a ring, a matrix model of the truncated skew polynomial ring
`K[u; σ] / (u ^ (n + 1))`; let `G` be its group of units with all diagonal entries `1`. Let `G_k`
be the subgroup of the `g ∈ G` such that `g - 1` vanishes below the `k`-th superdiagonal, and let
`λ_k g` be the entry of `g - 1` in row `0` and column `k`. For `g ∈ G_m` and `h ∈ G_l` the
commutator `⁅g, h⁆` lies in `G_(m + l)` and
`λ_(m + l) ⁅g, h⁆ = λ_m g * σ ^ m (λ_l h) - λ_l h * σ ^ l (λ_m g)`.

Every equation `a * z ^ 2 - b * z = c` with `a ≠ 0` has a root in `K`. Hence, for `x ∈ G` with
`λ_1 x ≠ 0`, conjugating by suitable elements of `G_1, G_2, …, G_(n - 1)` in turn changes the
coefficients of `x` at levels `2, 3, …, n` in any prescribed way: the conjugacy class of `x` is
`x G_2`. It follows that `G_2` is the commutator subgroup, so `G` has the Camina property. The
filtration shows that `G` is nilpotent of class at most `n`, and the iterated commutators of two
suitable elements of `G_1` show that its class is exactly `n`. The group `G` is infinite: by the
theorem of Dark and Scoppola quoted above, finite examples have class at most 3.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.NilpotentCaminaClassUnboundedKourovka17Problem47Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 17.47 (S. H. Ghate, A. S. Muktibodh).
UnsolvedMath record UM-00701349 (`KOU-17.47`), dataset ulamai/UnsolvedMath v1.8.0.

`[G, G]` is `commutator G` and the class is `Group.nilpotencyClass`; groups are taken in `Type`.
-/

/-- **Bounded class for nilpotent Camina-type groups.** Kourovka Problem 17.47 (S. H. Ghate,
A. S. Muktibodh) asks whether this proposition holds: there is a natural number $c$ such that
every nilpotent group $G$ in which, for every $x \notin [G, G]$, the coset $x[G, G]$ of the
commutator subgroup $[G, G]$ equals the conjugacy class $x^G$ of $x$, has nilpotency class at
most $c$. -/
def nilpotentCaminaClassBounded : Prop :=
  ∃ c : ℕ, ∀ (G : Type) [Group G], Group.IsNilpotent G →
    (∀ x : G, x ∉ commutator G →
      ∀ y : G, (∃ z ∈ commutator G, y = x * z) ↔ ∃ g : G, y = g * x * g⁻¹) →
    Group.nilpotencyClass G ≤ c

open Matrix commutatorElement

section Construction

variable {K : Type*} [Field K] {n : ℕ}

/-- The matrices vanishing below the `m`-th superdiagonal. -/
private def band (n m : ℕ) : AddSubgroup (Matrix (Fin (n + 1)) (Fin (n + 1)) K) where
  carrier := {M | ∀ i j : Fin (n + 1), (j : ℕ) < (i : ℕ) + m → M i j = 0}
  add_mem' {a b} ha hb i j h := by simp [ha i j h, hb i j h]
  zero_mem' _ _ _ := rfl
  neg_mem' {a} ha i j h := by simp [ha i j h]

private theorem band_mul {m l : ℕ} {M N : Matrix (Fin (n + 1)) (Fin (n + 1)) K}
    (hM : M ∈ band n m) (hN : N ∈ band n l) : M * N ∈ band n (m + l) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : (k : ℕ) < (i : ℕ) + m
  · rw [hM i k hk, zero_mul]
  · rw [hN k j (by omega), mul_zero]

private theorem band_anti {m l : ℕ} (h : m ≤ l) {M : Matrix (Fin (n + 1)) (Fin (n + 1)) K}
    (hM : M ∈ band n l) : M ∈ band n m :=
  fun i j hij => hM i j (by omega)

private theorem eq_zero_of_mem_band {m : ℕ} (hm : n + 1 ≤ m)
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) K} (hM : M ∈ band n m) : M = 0 := by
  ext i j
  exact hM i j (by omega)

private theorem one_mem_band_zero : (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K) ∈ band n 0 := by
  intro i j h
  rw [Matrix.one_apply_ne]
  rintro rfl
  omega

private theorem pow_mem_band {m : ℕ} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) K}
    (hM : M ∈ band n m) : ∀ k : ℕ, M ^ k ∈ band n (k * m)
  | 0 => by simpa using one_mem_band_zero
  | k + 1 => by
    rw [pow_succ, Nat.succ_mul]
    exact band_mul (pow_mem_band hM k) hM

variable (σ : K →+* K)

/-- The upper triangular matrices whose entries move by `σ` one step down each diagonal: a matrix
model of the truncated skew polynomial ring `K[u; σ] / (u ^ (n + 1))`. -/
private def twisted (n : ℕ) : Subring (Matrix (Fin (n + 1)) (Fin (n + 1)) K) where
  carrier := {M | M ∈ band n 0 ∧ ∀ i j : Fin n, M i.succ j.succ = σ (M i.castSucc j.castSucc)}
  mul_mem' := by
    rintro M N ⟨hMb, hMt⟩ ⟨hNb, hNt⟩
    refine ⟨by simpa using band_mul hMb hNb, fun i j => ?_⟩
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_castSucc,
      hMb i.succ 0 (by simp), hNb (Fin.last n) j.castSucc (by simp), zero_mul, mul_zero,
      zero_add, add_zero, map_sum]
    simp only [hMt, hNt, map_mul]
  one_mem' := by
    refine ⟨one_mem_band_zero, fun i j => ?_⟩
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  add_mem' := by
    rintro M N ⟨hMb, hMt⟩ ⟨hNb, hNt⟩
    exact ⟨add_mem hMb hNb, fun i j => by simp [hMt, hNt]⟩
  zero_mem' := ⟨zero_mem _, fun i j => by simp⟩
  neg_mem' := by
    rintro M ⟨hMb, hMt⟩
    exact ⟨neg_mem hMb, fun i j => by simp [hMt]⟩

/-- In a matrix of `twisted σ n`, the entry `(i, i + k)` is `σ ^ i` of the entry `(0, k)`. -/
private theorem twisted_diag {M : Matrix (Fin (n + 1)) (Fin (n + 1)) K} (hM : M ∈ twisted σ n) :
    ∀ (i k : ℕ) (h : i + k < n + 1),
      M ⟨i, by omega⟩ ⟨i + k, h⟩ = (σ ^ i) (M 0 ⟨k, by omega⟩)
  | 0, k, h => by simp
  | i + 1, k, h => by
    have key : M ⟨i + 1, by omega⟩ ⟨i + 1 + k, h⟩ =
        σ (M ⟨i, by omega⟩ ⟨i + k, by omega⟩) := by
      have e : (⟨i + 1 + k, h⟩ : Fin (n + 1)) = (⟨i + k, by omega⟩ : Fin n).succ :=
        Fin.ext (by change i + 1 + k = i + k + 1; omega)
      rw [e]
      exact hM.2 ⟨i, by omega⟩ ⟨i + k, by omega⟩
    rw [key, twisted_diag hM i k (by omega), pow_succ']
    rfl

/-- The entry of a matrix in row `0` and column `k`, or `0` when `k` is out of range. -/
private def ent (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (k : ℕ) : K :=
  if h : k < n + 1 then M 0 ⟨k, h⟩ else 0

omit σ in
private theorem ent_add (M N : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (k : ℕ) :
    ent (M + N) k = ent M k + ent N k := by
  unfold ent; split_ifs <;> simp

omit σ in
private theorem ent_sub (M N : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (k : ℕ) :
    ent (M - N) k = ent M k - ent N k := by
  unfold ent; split_ifs <;> simp

omit σ in
private theorem ent_zero (k : ℕ) : ent (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) K) k = 0 := by
  unfold ent; split_ifs <;> simp

omit σ in
private theorem ent_eq_zero_of_mem_band {M : Matrix (Fin (n + 1)) (Fin (n + 1)) K} {k : ℕ}
    (hM : M ∈ band n (k + 1)) : ent M k = 0 := by
  unfold ent
  split_ifs with h
  · exact hM 0 ⟨k, h⟩ (by simp)
  · rfl

private theorem mem_band_succ {M : Matrix (Fin (n + 1)) (Fin (n + 1)) K} {k : ℕ}
    (hMt : M ∈ twisted σ n) (hM : M ∈ band n k) (h0 : ent M k = 0) : M ∈ band n (k + 1) := by
  rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
  simp only at hij
  rcases Nat.lt_or_ge j (i + k) with h | h
  · exact hM _ _ h
  · obtain rfl : j = i + k := by omega
    rw [twisted_diag σ hMt i k hj]
    unfold ent at h0
    rw [dite_eq_left (by omega)] at h0
    rw [h0, map_zero]

private theorem ent_mul {M N : Matrix (Fin (n + 1)) (Fin (n + 1)) K} {m l : ℕ}
    (hM : M ∈ band n m) (hN : N ∈ band n l) (hNt : N ∈ twisted σ n) (hml : m + l < n + 1) :
    ent (M * N) (m + l) = ent M m * (σ ^ m) (ent N l) := by
  unfold ent
  rw [dite_eq_left hml, dite_eq_left (by omega), dite_eq_left (by omega), Matrix.mul_apply,
    Finset.sum_eq_single (⟨m, by omega⟩ : Fin (n + 1))]
  · rw [twisted_diag σ hNt m l hml]
  · rintro ⟨k, hk⟩ _ hne
    rcases Nat.lt_or_ge k m with h | h
    · rw [hM 0 ⟨k, hk⟩ (by simpa using h), zero_mul]
    · have : k ≠ m := fun e => hne (Fin.ext e)
      rw [hN ⟨k, hk⟩ ⟨m + l, hml⟩ (by simp only; omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The units of `twisted σ n` whose diagonal entries are all `1`. -/
private def caminaGroup (n : ℕ) : Subgroup (Matrix (Fin (n + 1)) (Fin (n + 1)) K)ˣ where
  carrier := {U | (U : Matrix (Fin (n + 1)) (Fin (n + 1)) K) ∈ twisted σ n ∧
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) K) - 1 ∈ band n 1}
  one_mem' := ⟨Subring.one_mem _, by simp⟩
  mul_mem' := by
    rintro U V ⟨hUt, hUb⟩ ⟨hVt, hVb⟩
    refine ⟨by simpa using Subring.mul_mem _ hUt hVt, ?_⟩
    have e : ((U * V : (Matrix (Fin (n + 1)) (Fin (n + 1)) K)ˣ) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) K) - 1 =
        ((U : Matrix (Fin (n + 1)) (Fin (n + 1)) K) - 1) *
          ((V : Matrix (Fin (n + 1)) (Fin (n + 1)) K) - 1) +
          ((U : Matrix (Fin (n + 1)) (Fin (n + 1)) K) - 1) +
          ((V : Matrix (Fin (n + 1)) (Fin (n + 1)) K) - 1) := by
      rw [Units.val_mul]; noncomm_ring
    rw [e]
    exact add_mem (add_mem (band_anti (by omega) (band_mul hUb hVb)) hUb) hVb
  inv_mem' := by
    rintro U ⟨hUt, hUb⟩
    set x : Matrix (Fin (n + 1)) (Fin (n + 1)) K := 1 - U with hxdef
    have hx : x ∈ band n 1 := by
      have := neg_mem hUb
      rwa [neg_sub] at this
    have hxt : x ∈ twisted σ n := Subring.sub_mem _ (Subring.one_mem _) hUt
    have hxn : x ^ (n + 1) = 0 :=
      eq_zero_of_mem_band le_rfl (by simpa using pow_mem_band hx (n + 1))
    have hinv : ((U⁻¹ : (Matrix (Fin (n + 1)) (Fin (n + 1)) K)ˣ) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) K) = ∑ i ∈ Finset.range (n + 1), x ^ i := by
      apply Units.inv_eq_of_mul_eq_one_left
      have := geom_sum_mul_neg x (n + 1)
      rwa [hxn, sub_zero, hxdef, sub_sub_cancel] at this
    have hSt : ((U⁻¹ : (Matrix (Fin (n + 1)) (Fin (n + 1)) K)ˣ) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) K) ∈ twisted σ n := by
      rw [hinv]
      exact Subring.sum_mem _ fun i _ => Subring.pow_mem _ hxt i
    refine ⟨hSt, ?_⟩
    have e : ((U⁻¹ : (Matrix (Fin (n + 1)) (Fin (n + 1)) K)ˣ) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) K) - 1 =
        ((U⁻¹ : (Matrix (Fin (n + 1)) (Fin (n + 1)) K)ˣ) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) K) * x := by
      rw [hxdef, mul_sub, mul_one, Units.inv_mul]
    rw [e]
    simpa using band_mul hSt.1 hx

/-- The matrix of an element of `caminaGroup σ n`. -/
private abbrev mat (g : caminaGroup σ n) : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  ((g : (Matrix (Fin (n + 1)) (Fin (n + 1)) K)ˣ) : Matrix (Fin (n + 1)) (Fin (n + 1)) K)

private theorem mat_mul (g h : caminaGroup σ n) : mat σ (g * h) = mat σ g * mat σ h := rfl

private theorem mat_one : mat σ (1 : caminaGroup σ n) = 1 := rfl

private theorem mat_mul_inv (g : caminaGroup σ n) : mat σ g * mat σ g⁻¹ = 1 :=
  Units.mul_inv (g : (Matrix (Fin (n + 1)) (Fin (n + 1)) K)ˣ)

private theorem mat_inv_mul (g : caminaGroup σ n) : mat σ g⁻¹ * mat σ g = 1 :=
  Units.inv_mul (g : (Matrix (Fin (n + 1)) (Fin (n + 1)) K)ˣ)

private theorem mat_mem_twisted (g : caminaGroup σ n) : mat σ g ∈ twisted σ n := g.2.1

private theorem mat_sub_one_mem_twisted (g : caminaGroup σ n) : mat σ g - 1 ∈ twisted σ n :=
  Subring.sub_mem _ (mat_mem_twisted σ g) (Subring.one_mem _)

private theorem mat_injective {g h : caminaGroup σ n} (e : mat σ g = mat σ h) : g = h :=
  Subtype.ext (Units.ext e)

/-- The elements `g` of `caminaGroup σ n` such that `g - 1` vanishes below the `k`-th
superdiagonal. -/
private def filt (k : ℕ) : Subgroup (caminaGroup σ n) where
  carrier := {g | mat σ g - 1 ∈ band n k}
  one_mem' := by
    change mat σ 1 - 1 ∈ band n k
    rw [mat_one, sub_self]
    exact zero_mem _
  mul_mem' := by
    intro g h hg hh
    change mat σ g - 1 ∈ band n k at hg
    change mat σ h - 1 ∈ band n k at hh
    change mat σ (g * h) - 1 ∈ band n k
    have e : mat σ (g * h) - 1 =
        (mat σ g - 1) * (mat σ h - 1) + (mat σ g - 1) + (mat σ h - 1) := by
      rw [mat_mul]; noncomm_ring
    rw [e]
    exact add_mem (add_mem (band_anti (by omega) (band_mul hg hh)) hg) hh
  inv_mem' := by
    intro g hg
    change mat σ g - 1 ∈ band n k at hg
    change mat σ g⁻¹ - 1 ∈ band n k
    have e : mat σ g⁻¹ - 1 = -(mat σ g⁻¹ * (mat σ g - 1)) := by
      rw [mul_sub, mat_inv_mul, mul_one, neg_sub]
    rw [e]
    exact neg_mem (by simpa using band_mul (mat_mem_twisted σ g⁻¹).1 hg)

private theorem mem_filt {k : ℕ} {g : caminaGroup σ n} :
    g ∈ filt σ k ↔ mat σ g - 1 ∈ band n k :=
  Iff.rfl

private theorem filt_one (g : caminaGroup σ n) : g ∈ filt σ 1 := g.2.2

private theorem filt_anti {m k : ℕ} (h : m ≤ k) : filt σ (n := n) k ≤ filt σ m :=
  fun _ hg => band_anti h hg

private theorem eq_one_of_mem_filt {k : ℕ} (hk : n + 1 ≤ k) {g : caminaGroup σ n}
    (hg : g ∈ filt σ k) : g = 1 :=
  mat_injective σ (sub_eq_zero.mp (eq_zero_of_mem_band hk hg))

/-- The level-`k` coefficient of an element: the entry of `g - 1` in row `0` and column `k`. -/
private def lead (k : ℕ) (g : caminaGroup σ n) : K := ent (mat σ g - 1) k

private theorem lead_one (k : ℕ) : lead σ k (1 : caminaGroup σ n) = 0 := by
  rw [lead, mat_one, sub_self, ent_zero]

private theorem lead_eq_zero_of_mem {k : ℕ} {g : caminaGroup σ n} (hg : g ∈ filt σ (k + 1)) :
    lead σ k g = 0 :=
  ent_eq_zero_of_mem_band hg

private theorem mem_filt_succ {k : ℕ} {g : caminaGroup σ n} (hg : g ∈ filt σ k)
    (h0 : lead σ k g = 0) : g ∈ filt σ (k + 1) :=
  mem_band_succ σ (mat_sub_one_mem_twisted σ g) hg h0

private theorem lead_mul {k : ℕ} (hk : 1 ≤ k) {g h : caminaGroup σ n} (hg : g ∈ filt σ k)
    (hh : h ∈ filt σ k) : lead σ k (g * h) = lead σ k g + lead σ k h := by
  have e : mat σ (g * h) - 1 =
      (mat σ g - 1) * (mat σ h - 1) + (mat σ g - 1) + (mat σ h - 1) := by
    rw [mat_mul]; noncomm_ring
  rw [lead, e, ent_add, ent_add,
    ent_eq_zero_of_mem_band (band_anti (by omega) (band_mul hg hh)), zero_add]
  rfl

/-- The commutator of `g ∈ G_m` and `h ∈ G_l` lies in `G_(m + l)`, with level-`(m + l)`
coefficient `λ_m g * σ ^ m (λ_l h) - λ_l h * σ ^ l (λ_m g)`. -/
private theorem commutator_mem_filt {m l : ℕ} {g h : caminaGroup σ n} (hg : g ∈ filt σ m)
    (hh : h ∈ filt σ l) :
    ⁅g, h⁆ ∈ filt σ (m + l) ∧ (m + l < n + 1 → lead σ (m + l) ⁅g, h⁆ =
      lead σ m g * (σ ^ m) (lead σ l h) - lead σ l h * (σ ^ l) (lead σ m g)) := by
  set C := (mat σ g - 1) * (mat σ h - 1) - (mat σ h - 1) * (mat σ g - 1) with hCdef
  set w := mat σ (g⁻¹ * h⁻¹) - 1 with hwdef
  have e : mat σ ⁅g, h⁆ - 1 = C + C * w := by
    have h1 := mat_mul_inv σ g
    have h2 := mat_mul_inv σ h
    rw [commutatorElement_def, mat_mul, mat_mul, mat_mul, hCdef, hwdef, mat_mul]
    calc mat σ g * mat σ h * mat σ g⁻¹ * mat σ h⁻¹ - 1
        = mat σ g * mat σ h * mat σ g⁻¹ * mat σ h⁻¹ - mat σ h * (mat σ g * mat σ g⁻¹) *
            mat σ h⁻¹ := by rw [h1, mul_one, h2]
      _ = _ := by noncomm_ring
  have hC : C ∈ band n (m + l) :=
    sub_mem (band_mul hg hh) (by have := band_mul hh hg; rwa [Nat.add_comm l m] at this)
  have hCw : C * w ∈ band n (m + l + 1) := band_mul hC (filt_one σ (g⁻¹ * h⁻¹))
  refine ⟨?_, fun hml => ?_⟩
  · rw [mem_filt, e]
    exact add_mem hC (band_anti (by omega) hCw)
  · rw [lead, e, ent_add, ent_eq_zero_of_mem_band hCw, add_zero, hCdef, ent_sub,
      ent_mul σ hg hh (mat_sub_one_mem_twisted σ h) hml, add_comm m l,
      ent_mul σ hh hg (mat_sub_one_mem_twisted σ g) (by omega)]
    rfl

/-- The matrix with `σ ^ i z` in position `(i, i + k)` and zeros elsewhere. -/
private def diagMat (k : ℕ) (z : K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  Matrix.of fun i j => if (j : ℕ) = i + k then (σ ^ (i : ℕ)) z else 0

private theorem diagMat_mem_twisted (k : ℕ) (z : K) : diagMat σ (n := n) k z ∈ twisted σ n := by
  refine ⟨fun i j h => ?_, fun i j => ?_⟩
  · simp only [diagMat, Matrix.of_apply]
    rw [ite_eq_right (by omega)]
  · simp only [diagMat, Matrix.of_apply, Fin.val_succ, Fin.val_castSucc]
    split_ifs with h1 h2 h2
    · rw [pow_succ']; rfl
    · omega
    · omega
    · simp

private theorem diagMat_mem_band (k : ℕ) (z : K) : diagMat σ (n := n) k z ∈ band n k := by
  intro i j h
  simp only [diagMat, Matrix.of_apply]
  rw [ite_eq_right (by omega)]

private theorem ent_diagMat {k : ℕ} (hk : k < n + 1) (z : K) :
    ent (diagMat σ (n := n) k z) k = z := by
  unfold ent
  rw [dite_eq_left hk]
  simp [diagMat]

/-- The element of `caminaGroup σ n` with matrix `1 + M`. -/
private noncomputable def mkElt (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hMt : M ∈ twisted σ n) (hMb : M ∈ band n 1) : caminaGroup σ n :=
  ⟨(IsNilpotent.isUnit_one_add
      ⟨n + 1, eq_zero_of_mem_band le_rfl (by simpa using pow_mem_band hMb (n + 1))⟩).unit,
    ⟨Subring.add_mem _ (Subring.one_mem _) hMt, by simpa using hMb⟩⟩

private theorem mat_mkElt (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hMt : M ∈ twisted σ n)
    (hMb : M ∈ band n 1) : mat σ (mkElt σ M hMt hMb) = 1 + M := rfl

private theorem exists_elt (k : ℕ) (hk1 : 1 ≤ k) (hk : k < n + 1) (z : K) :
    ∃ g : caminaGroup σ n, g ∈ filt σ k ∧ lead σ k g = z := by
  refine ⟨mkElt σ (diagMat σ k z) (diagMat_mem_twisted σ k z)
    (band_anti hk1 (diagMat_mem_band σ k z)), ?_, ?_⟩
  · rw [mem_filt, mat_mkElt, add_sub_cancel_left]
    exact diagMat_mem_band σ k z
  · rw [lead, mat_mkElt, add_sub_cancel_left, ent_diagMat σ hk]

private theorem lead_one_conj (g x : caminaGroup σ n) :
    lead σ 1 (g * x * g⁻¹) = lead σ 1 x := by
  have e : g * x * g⁻¹ = ⁅g, x⁆ * x := by rw [commutatorElement_def]; group
  have hc := (commutator_mem_filt σ (filt_one σ g) (filt_one σ x)).1
  rw [e, lead_mul σ le_rfl (filt_anti σ (by omega) hc) (filt_one σ x),
    lead_eq_zero_of_mem σ hc, zero_add]

private theorem lead_one_inv (x : caminaGroup σ n) : lead σ 1 x⁻¹ = -lead σ 1 x := by
  have := lead_mul σ le_rfl (filt_one σ x⁻¹) (filt_one σ x)
  rw [inv_mul_cancel, lead_one] at this
  linear_combination -this

/-- If `λ_1 x ≠ 0`, then every element of `x G_2` is conjugate to `x`: conjugation by suitable
elements of `G_1, G_2, …` corrects the coefficients of `x` one level at a time. -/
private theorem conj_core (hσ : ∀ a b c : K, a ≠ 0 → ∃ z, a * σ z - b * z = c)
    (x : caminaGroup σ n) (hx : lead σ 1 x ≠ 0) (w : caminaGroup σ n) (hw : w ∈ filt σ 2) :
    ∃ g : caminaGroup σ n, g * x * g⁻¹ = x * w := by
  have key : ∀ k : ℕ, ∃ g : caminaGroup σ n, (g * x * g⁻¹)⁻¹ * (x * w) ∈ filt σ (k + 2) := by
    intro k
    induction k with
    | zero => exact ⟨1, by simpa using hw⟩
    | succ k ih =>
      obtain ⟨g, hg⟩ := ih
      by_cases hk : k + 2 < n + 1
      · set y := g * x * g⁻¹ with hy
        set E := y⁻¹ * (x * w) with hE
        have hya : lead σ 1 y = lead σ 1 x := lead_one_conj σ g x
        obtain ⟨z, hz⟩ :=
          hσ (lead σ 1 x) ((σ ^ (k + 1)) (lead σ 1 x)) (-lead σ (k + 2) E) hx
        obtain ⟨h, hh, hhz⟩ := exists_elt σ (n := n) (k + 1) (by omega) (by omega) z
        refine ⟨h * g, ?_⟩
        have e : (h * g * x * (h * g)⁻¹)⁻¹ * (x * w) = ⁅h, y⁻¹⁆ * E := by
          simp only [hy, hE, commutatorElement_def]; group
        rw [e]
        have hc := commutator_mem_filt σ hh (filt_one σ y⁻¹)
        apply mem_filt_succ σ (mul_mem hc.1 hg)
        rw [lead_mul σ (by omega) hc.1 hg, hc.2 (by omega), hhz, lead_one_inv, hya, map_neg,
          pow_one]
        linear_combination hz
      · exact ⟨g, by rw [eq_one_of_mem_filt σ (by omega) hg]; exact one_mem _⟩
  obtain ⟨g, hg⟩ := key n
  exact ⟨g, inv_mul_eq_one.mp (eq_one_of_mem_filt σ (by omega) hg)⟩

private theorem lowerCentralSeries_le_filt (k : ℕ) :
    (⊤ : Subgroup (caminaGroup σ n)).lowerCentralSeries k ≤ filt σ (k + 1) := by
  induction k with
  | zero => intro g _; exact filt_one σ g
  | succ k ih =>
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_le]
    intro g hg h _
    exact (commutator_mem_filt σ (ih hg) (filt_one σ h)).1

private theorem isNilpotent : Group.IsNilpotent (caminaGroup σ n) :=
  Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨n, eq_bot_iff.mpr fun _ hg =>
    (Subgroup.mem_bot).mpr (eq_one_of_mem_filt σ le_rfl (lowerCentralSeries_le_filt σ n hg))⟩

private theorem commutator_le_filt_two : commutator (caminaGroup σ n) ≤ filt σ 2 :=
  Subgroup.commutator_le.mpr fun g _ h _ =>
    (commutator_mem_filt σ (filt_one σ g) (filt_one σ h)).1

private theorem filt_two_le_commutator (hσ : ∀ a b c : K, a ≠ 0 → ∃ z, a * σ z - b * z = c)
    (hn : 1 ≤ n) : filt σ 2 ≤ commutator (caminaGroup σ n) := by
  intro w hw
  obtain ⟨u, -, hu⟩ := exists_elt σ (n := n) 1 le_rfl (by omega) 1
  obtain ⟨g, hg⟩ := conj_core σ hσ u (by rw [hu]; exact one_ne_zero) w hw
  have e : w = ⁅u⁻¹, g⁆ := by
    calc w = u⁻¹ * (u * w) := by group
      _ = u⁻¹ * (g * u * g⁻¹) := by rw [hg]
      _ = ⁅u⁻¹, g⁆ := by rw [commutatorElement_def]; group
  rw [e]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- The Camina property of `caminaGroup σ n`. -/
private theorem camina (hσ : ∀ a b c : K, a ≠ 0 → ∃ z, a * σ z - b * z = c) (hn : 1 ≤ n) :
    ∀ x : caminaGroup σ n, x ∉ commutator (caminaGroup σ n) →
      ∀ y : caminaGroup σ n, (∃ z ∈ commutator (caminaGroup σ n), y = x * z) ↔
        ∃ g : caminaGroup σ n, y = g * x * g⁻¹ := by
  intro x hx y
  have hx1 : lead σ 1 x ≠ 0 := fun h =>
    hx (filt_two_le_commutator σ hσ hn (mem_filt_succ σ (filt_one σ x) h))
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨g, hg⟩ := conj_core σ hσ x hx1 z (commutator_le_filt_two σ hz)
    exact ⟨g, hg.symm⟩
  · rintro ⟨g, rfl⟩
    exact ⟨⁅x⁻¹, g⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
      (Subgroup.mem_top _), by rw [commutatorElement_def]; group⟩

/-- The `c`-th term of the lower central series of `caminaGroup σ (c + 1)` is not trivial. -/
private theorem lowerCentralSeries_ne_bot (hσ : ∀ a b c : K, a ≠ 0 → ∃ z, a * σ z - b * z = c)
    (c : ℕ) : (⊤ : Subgroup (caminaGroup σ (c + 1))).lowerCentralSeries c ≠ ⊥ := by
  have hτ : Function.Surjective (fun z : K => z - σ z) := by
    intro d
    obtain ⟨z, hz⟩ := hσ 1 1 (-d) one_ne_zero
    exact ⟨z, by linear_combination -hz⟩
  obtain ⟨b, hb⟩ := (hτ.iterate c) 1
  obtain ⟨u, hu1, hu⟩ := exists_elt σ (n := c + 1) 1 le_rfl (by omega) (1 : K)
  obtain ⟨y0, hy01, hy0⟩ := exists_elt σ (n := c + 1) 1 le_rfl (by omega) b
  let y : ℕ → caminaGroup σ (c + 1) := fun j => Nat.rec y0 (fun _ v => ⁅v, u⁆) j
  have hy : ∀ j ≤ c, y j ∈ (⊤ : Subgroup (caminaGroup σ (c + 1))).lowerCentralSeries j ∧
      y j ∈ filt σ (j + 1) ∧ lead σ (j + 1) (y j) = (fun z : K => z - σ z)^[j] b := by
    intro j
    induction j with
    | zero => intro _; exact ⟨Subgroup.mem_top _, hy01, hy0⟩
    | succ j ih =>
      intro hj
      obtain ⟨h1, h2, h3⟩ := ih (by omega)
      have hc := commutator_mem_filt σ h2 hu1
      refine ⟨Subgroup.commutator_mem_commutator h1 (Subgroup.mem_top u), hc.1, ?_⟩
      rw [show y (j + 1) = ⁅y j, u⁆ from rfl, hc.2 (by omega), h3, hu, map_one, mul_one,
        one_mul, pow_one, Function.iterate_succ_apply']
  obtain ⟨h1, -, h3⟩ := hy c le_rfl
  rw [hb] at h3
  intro hbot
  rw [hbot, Subgroup.mem_bot] at h1
  rw [h1, lead_one] at h3
  exact zero_ne_one h3

end Construction

/-- Over the algebraic closure of `ZMod 2`, every equation `a * z ^ 2 - b * z = c` with `a ≠ 0`
has a solution. -/
private theorem frobenius_solvable (a b c : AlgebraicClosure (ZMod 2)) (ha : a ≠ 0) :
    ∃ z, a * frobenius (AlgebraicClosure (ZMod 2)) 2 z - b * z = c := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root
    (Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C (-b) * Polynomial.X + Polynomial.C (-c))
    (by rw [Polynomial.degree_quadratic ha]; decide)
  refine ⟨z, ?_⟩
  simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X] at hz
  change a * z ^ 2 - b * z = c
  linear_combination hz

/--
**Nilpotent Camina-type groups have unbounded class.** There is no natural number $c$ such that
every nilpotent group $G$ in which, for every $x \notin [G, G]$, the coset $x[G, G]$ of the
commutator subgroup $[G, G]$ equals the conjugacy class $x^G$ of $x$, has nilpotency class at
most $c$. So Kourovka Problem 17.47 has a negative answer.

Ionin and Semidetnov (Answer 4.2) construct, for every integer $c \ge 2$, a nilpotent group of
class exactly $c$ in which $x^G = x[G, G]$ for every $x \notin [G, G]$. The Kourovka Notebook
(21st issue) answers 17.47 "No, there is no such bound".

Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Problem 17.47 (S. H. Ghate, A. S. Muktibodh); resolution: V. Ionin and A. Semidetnov, On
some more problems from the Kourovka Notebook, preprint, arXiv:2608.29219 (2026; solutions found
with the assistance of large language models and checked by the authors, per its abstract), Answer
4.2 (for every integer c ≥ 2 there exists a nilpotent Camina group of class exactly c); the Kourovka
Notebook (21st issue) marks 17.47 solved (No, there is no such bound),
https://arxiv.org/abs/2608.29219.
-/
theorem nilpotentCaminaClassBounded_refuted : ¬ nilpotentCaminaClassBounded := by
  rintro ⟨c, hc⟩
  let σ := frobenius (AlgebraicClosure (ZMod 2)) 2
  have := isNilpotent σ (n := c + 1)
  have h := hc (caminaGroup σ (c + 1)) this (camina σ frobenius_solvable (by omega))
  exact lowerCentralSeries_ne_bot σ frobenius_solvable c
    (Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr h)

end MathlibExt.GroupTheory.NilpotentCaminaClassUnboundedKourovka17Problem47Wanted
