/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_
of_forall_ker_le_pow_smul_top.lean`
and
`P2M/Sol/S_IsAdicComplete_finite_and_surjective_and_apply_eq_zero_iff_
of_forall_ker_le_pow_smul_top.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Finiteness.Basic

@[expose] public section

universe u v

open Function

namespace FormalGAGAFiniteLimitAux

private abbrev Ψ (R : Type u) [CommRing R] {M : ℕ → Type v} [∀ n, AddCommGroup (M n)]
    [∀ n, Module R (M n)] {ι : Type} [Fintype ι] (g : ι → ∀ k, M k) (k : ℕ) :
    (ι → R) →ₗ[R] M k :=
  Fintype.linearCombination R (fun i => g i k)

variable {R : Type u} [CommRing R]
  {M : ℕ → Type v} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  (t : ∀ n : ℕ, M (n + 1) →ₗ[R] M n)

private theorem exists_partial (n : ℕ) (y : M n) :
    ∃ x : ∀ k, M k, (∀ k, k < n → t k (x (k + 1)) = x k) ∧ x n = y := by
  induction n with
  | zero =>
    refine ⟨Function.update 0 0 y, fun k hk => (Nat.not_lt_zero k hk).elim, ?_⟩
    simp
  | succ n ih =>
    obtain ⟨x, hx, hxn⟩ := ih (t n y)
    refine ⟨Function.update x (n + 1) y, fun k hk => ?_, by simp⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
    · have h1 : k + 1 ≠ n + 1 := by omega
      have h2 : k ≠ n + 1 := by omega
      rw [Function.update_of_ne h1, Function.update_of_ne h2]
      exact hx k hk'
    · have h2 : k ≠ k + 1 := by omega
      rw [Function.update_self, Function.update_of_ne h2, hxn]

private theorem update_compat {m : ℕ} (s : M m → M (m + 1)) (hs : ∀ z, t m (s z) = z)
    (z : ∀ k, M k) (hz : ∀ k, k < m → t k (z (k + 1)) = z k) :
    ∀ k, k < m + 1 → t k (Function.update z (m + 1) (s (z m)) (k + 1)) =
      Function.update z (m + 1) (s (z m)) k := by
  intro k hk
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
  · have h1 : k + 1 ≠ m + 1 := by omega
    have h2 : k ≠ m + 1 := by omega
    rw [Function.update_of_ne h1, Function.update_of_ne h2]
    exact hz k hk'
  · have h2 : k ≠ k + 1 := by omega
    rw [Function.update_self, Function.update_of_ne h2, hs]

private theorem exists_forall_eq_of_surjective (ht : ∀ n, Surjective (t n)) (n : ℕ) (y : M n) :
    ∃ x : ∀ k, M k, (∀ k, t k (x (k + 1)) = x k) ∧ x n = y := by
  obtain ⟨x, hx, hxn⟩ := exists_partial t n y
  have hs : ∀ k, ∃ s : M k → M (k + 1), ∀ z, t k (s z) = z := fun k =>
    ⟨surjInv (ht k), surjInv_eq (ht k)⟩
  choose s hs using hs
  let G : ∀ j : ℕ, {z : ∀ k, M k // ∀ k, k < n + j → t k (z (k + 1)) = z k} :=
    fun j => Nat.rec (motive := fun j => {z : ∀ k, M k // ∀ k, k < n + j → t k (z (k + 1)) = z k})
      ⟨x, hx⟩
      (fun j zj => ⟨Function.update zj.1 (n + j + 1) (s (n + j) (zj.1 (n + j))),
        update_compat t (s (n + j)) (hs (n + j)) zj.1 zj.2⟩) j
  have hG_succ : ∀ j k, k ≤ n + j → (G (j + 1)).1 k = (G j).1 k := by
    intro j k hk
    have h2 : k ≠ n + j + 1 := by omega
    change Function.update (G j).1 (n + j + 1) _ k = _
    rw [Function.update_of_ne h2]
  have hG_le : ∀ j j', j ≤ j' → ∀ k, k ≤ n + j → (G j').1 k = (G j).1 k := by
    intro j j' hjj' k hk
    induction j', hjj' using Nat.le_induction with
    | base => rfl
    | succ j' hj' ih => rw [hG_succ j' k (by omega), ih]
  refine ⟨fun k => (G k).1 k, fun k => ?_, ?_⟩
  · rw [(G (k + 1)).2 k (by omega), hG_succ k k (by omega)]
  · change (G n).1 n = y
    rw [hG_le 0 n (Nat.zero_le n) n (by omega)]
    exact hxn

private theorem eq_of_eq_of_le {x x' : ∀ k, M k} (hx : ∀ k, t k (x (k + 1)) = x k)
    (hx' : ∀ k, t k (x' (k + 1)) = x' k) {m : ℕ} (h : x m = x' m) {k : ℕ} (hk : k ≤ m) :
    x k = x' k := by
  suffices H : ∀ d k, k + d = m → x k = x' k from H (m - k) k (by omega)
  intro d
  induction d with
  | zero => intro k hk; subst hk; simpa using h
  | succ d ih =>
    intro k hk
    rw [← hx k, ← hx' k, ih (k + 1) (by omega)]

variable (I : Ideal R)

private theorem span_range_apply_eq_top (hI : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (M n)) = ⊥)
    (hker : ∀ n : ℕ, LinearMap.ker (t n) ≤ I ^ (n + 1) • ⊤)
    {ι : Type*} (g : ι → ∀ k, M k) (hg : ∀ i k, t k (g i (k + 1)) = g i k)
    (h0 : Submodule.span R (Set.range fun i => g i 0) = ⊤) (n : ℕ) :
    Submodule.span R (Set.range fun i => g i n) = ⊤ := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    set N : Submodule R (M (n + 1)) := Submodule.span R (Set.range fun i => g i (n + 1)) with hN
    set J : Ideal R := I ^ (n + 1) with hJ
    have hmap : N.map (t n) = ⊤ := by
      rw [hN, Submodule.map_span, ← Set.range_comp]
      have : (t n) ∘ (fun i => g i (n + 1)) = fun i => g i n := funext fun i => hg i n
      rw [this, ih]
    have hsup : (⊤ : Submodule R (M (n + 1))) ≤ N ⊔ J • ⊤ := by
      intro y _
      have hy : t n y ∈ N.map (t n) := by rw [hmap]; exact Submodule.mem_top
      obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp hy
      have hker' : y - z ∈ LinearMap.ker (t n) := by
        rw [LinearMap.mem_ker, map_sub, hzy, sub_self]
      have : y = z + (y - z) := by abel
      rw [this]
      exact Submodule.add_mem_sup hz (hker n hker')
    have hJ2 : (J * J) • (⊤ : Submodule R (M (n + 1))) = ⊥ := by
      rw [eq_bot_iff, ← hI (n + 1), hJ, ← pow_add]
      exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
    have hJle : J • (⊤ : Submodule R (M (n + 1))) ≤ N := by
      calc J • (⊤ : Submodule R (M (n + 1))) ≤ J • (N ⊔ J • ⊤) := smul_mono_right J hsup
        _ = J • N ⊔ (J * J) • ⊤ := by rw [Submodule.smul_sup, Submodule.mul_smul]
        _ ≤ N ⊔ ⊥ := sup_le_sup Submodule.smul_le_right hJ2.le
        _ = N := sup_bot_eq N
    exact eq_top_iff.mpr (hsup.trans (sup_le le_rfl hJle))

private theorem apply_mem_of_mem_smul_top {ι : Type*} (J : Ideal R) {e : ι → R}
    (he : e ∈ J • (⊤ : Submodule R (ι → R))) (i : ι) : e i ∈ J := by
  refine Submodule.smul_induction_on (p := fun e : ι → R => e i ∈ J) he ?_ ?_
  · intro r hr x _
    simpa using J.mul_mem_right (x i) hr
  · intro x y hx hy
    simpa using J.add_mem hx hy

private theorem mem_smul_top_of_forall_apply_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Ideal R)
    {e : ι → R} (he : ∀ i, e i ∈ J) : e ∈ J • (⊤ : Submodule R (ι → R)) := by
  have : e = ∑ i, e i • (Pi.single i (1 : R) : ι → R) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (he i) Submodule.mem_top

private theorem mem_smul_top_self_iff (J : Ideal R) (x : R) :
    x ∈ (J • ⊤ : Submodule R R) ↔ x ∈ J := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top]

section Engine

variable [IsAdicComplete I R]
  (hI : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (M n)) = ⊥)
  (hker : ∀ n : ℕ, LinearMap.ker (t n) ≤ I ^ (n + 1) • ⊤)
  {ι : Type} [Fintype ι]
  (g : ι → ∀ k, M k) (hg : ∀ i k, t k (g i (k + 1)) = g i k)
  (hspan : ∀ n, Submodule.span R (Set.range fun i => g i n) = ⊤)

include hg in
private theorem t_Ψ (k : ℕ) (c : ι → R) : t k (Ψ R g (k + 1) c) = Ψ R g k c := by
  simp [Fintype.linearCombination_apply, map_sum, map_smul, hg]

include hspan in
private theorem Ψ_surjective (k : ℕ) : Surjective (Ψ R g k) :=
  (span_range_eq_top_iff_surjective_fintypeLinearCombination R _).mp (hspan k)

include hI hspan in
omit [IsAdicComplete I R] in
private theorem Ψ_eq_zero_of_forall_mem [DecidableEq ι] (k : ℕ) {e : ι → R}
    (he : ∀ i, e i ∈ I ^ (k + 1)) : Ψ R g k e = 0 := by
  have hmem : Ψ R g k e ∈ (I ^ (k + 1) • (⊤ : Submodule R (ι → R))).map (Ψ R g k) :=
    Submodule.mem_map_of_mem (mem_smul_top_of_forall_apply_mem _ he)
  rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr (Ψ_surjective g hspan k),
    hI k] at hmem
  simpa using hmem

include hker hg hspan in
omit [IsAdicComplete I R] in
private theorem exists_step (x : ∀ k, M k) (hx : ∀ k, t k (x (k + 1)) = x k) (k : ℕ) (c : ι → R)
    (hc : Ψ R g k c = x k) :
    ∃ e : ι → R, (∀ i, e i ∈ I ^ (k + 1)) ∧ Ψ R g (k + 1) (c + e) = x (k + 1) := by
  have hd : x (k + 1) - Ψ R g (k + 1) c ∈ LinearMap.ker (t k) := by
    rw [LinearMap.mem_ker, map_sub, hx, t_Ψ t g hg, hc, sub_self]
  have hd' := hker k hd
  rw [← LinearMap.range_eq_top.mpr (Ψ_surjective g hspan (k + 1)), ← Submodule.map_top,
    ← Submodule.map_smul''] at hd'
  obtain ⟨e, he, hed⟩ := Submodule.mem_map.mp hd'
  refine ⟨e, apply_mem_of_mem_smul_top _ he, ?_⟩
  rw [map_add, hed, add_sub_cancel]

include hI hker hg hspan in

private theorem exists_forall_Ψ_eq [DecidableEq ι] (x : ∀ k, M k) (hx : ∀ k, t k (x (k + 1)) = x k)
    (n : ℕ) (c₀ : ι → R) (hc₀ : Ψ R g n c₀ = x n) :
    ∃ c : ι → R, (∀ k, Ψ R g k c = x k) ∧ (∀ i, c i - c₀ i ∈ I ^ (n + 1)) := by

  have hstep : ∀ (k : ℕ) (c : {c : ι → R // Ψ R g k c = x k}),
      ∃ e : ι → R, (∀ i, e i ∈ I ^ (k + 1)) ∧ Ψ R g (k + 1) (c.1 + e) = x (k + 1) :=
    fun k c => exists_step t I hker g hg hspan x hx k c.1 c.2
  choose e he heΨ using hstep

  let C : ∀ j : ℕ, {c : ι → R // Ψ R g (n + j) c = x (n + j)} := fun j =>
    Nat.rec (motive := fun j => {c : ι → R // Ψ R g (n + j) c = x (n + j)}) ⟨c₀, hc₀⟩
      (fun j cj => ⟨cj.1 + e (n + j) cj, heΨ (n + j) cj⟩) j
  have hC0 : (C 0).1 = c₀ := rfl
  have hCsucc : ∀ j, (C (j + 1)).1 = (C j).1 + e (n + j) (C j) := fun j => rfl

  have hCdiff : ∀ (i : ι) (j j' : ℕ), j ≤ j' → (C j').1 i - (C j).1 i ∈ I ^ (n + j + 1) := by
    intro i j j' hjj'
    induction j', hjj' using Nat.le_induction with
    | base => simp
    | succ j' hj' ih =>
      have h1 : (C (j' + 1)).1 i - (C j).1 i =
          ((C j').1 i - (C j).1 i) + e (n + j') (C j') i := by
        rw [hCsucc]; simp only [Pi.add_apply]; ring
      rw [h1]
      exact Ideal.add_mem _ ih (Ideal.pow_le_pow_right (by omega) (he (n + j') (C j') i))

  have hlim : ∀ i, ∃ Li : R, ∀ j, Li - (C j).1 i ∈ I ^ (n + j + 1) := by
    intro i
    have hprec := IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete (I := I) (M := R))
      (f := fun j => (C j).1 i) (fun {m k} hmk => by
        rw [SModEq.sub_mem, mem_smul_top_self_iff]
        change (C m).1 i - (C k).1 i ∈ I ^ m
        have := Submodule.neg_mem _ (hCdiff i m k hmk)
        rw [neg_sub] at this
        exact Ideal.pow_le_pow_right (by omega) this)
    obtain ⟨Li, hLi⟩ := hprec
    refine ⟨Li, fun j => ?_⟩
    have h1 := hLi (n + j + 1)
    rw [SModEq.sub_mem, mem_smul_top_self_iff] at h1
    have h2 := hCdiff i j (n + j + 1) (by omega)
    have : Li - (C j).1 i =
        ((C (n + j + 1)).1 i - (C j).1 i) - ((C (n + j + 1)).1 i - Li) := by ring
    rw [this]
    exact Ideal.sub_mem _ h2 h1
  choose L hL using hlim
  refine ⟨L, fun k => ?_, fun i => by simpa [hC0] using hL i 0⟩

  have hhigh : ∀ j, Ψ R g (n + j) L = x (n + j) := by
    intro j
    have hsplit : L = (C j).1 + (L - (C j).1) := by abel
    rw [hsplit, map_add, (C j).2, Ψ_eq_zero_of_forall_mem I hI g hspan (n + j) (fun i => ?_),
      add_zero]
    simpa using hL i j

  rcases le_or_gt k n with hk | hk
  · exact eq_of_eq_of_le t (x := fun k => Ψ R g k L) (x' := x) (fun k => t_Ψ t g hg k L) hx
      (m := n) (by simpa using hhigh 0) hk
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk.le
    exact hhigh j

end Engine

end FormalGAGAFiniteLimitAux

open FormalGAGAFiniteLimitAux

namespace IsAdicComplete

/-- Finite limits of surjective inverse systems over an adically complete ring.

If `M n` is an inverse system with surjective transitions, every
`I ^ (n + 1)` annihilates `M n`, the kernels of the transitions lie in
`I ^ (n + 1) • ⊤`, and `M 0` is finite, then any submodule `L` of the product
cut out by the transition equations is finite, its projections are
surjective, and an element of `L` vanishes at level `n` exactly when it lies
in `I ^ (n + 1) • L`. -/
theorem finite_and_surjective_and_apply_eq_zero_iff_of_forall_ker_le_pow_smul_top
    {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : ℕ → Type v) [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (t : ∀ n : ℕ, M (n + 1) →ₗ[R] M n)
    (hI : ∀ n : ℕ, I ^ (n + 1) • (⊤ : Submodule R (M n)) = ⊥)
    (ht : ∀ n : ℕ, Function.Surjective (t n))
    (hker : ∀ n : ℕ, LinearMap.ker (t n) ≤ I ^ (n + 1) • ⊤)
    [Module.Finite R (M 0)]
    (L : Submodule R (∀ n, M n)) (hL : ∀ x, x ∈ L ↔ ∀ n, t n (x (n + 1)) = x n) :
    Module.Finite R L ∧
      (∀ (n : ℕ) (y : M n), ∃ x ∈ L, x n = y) ∧
      (∀ (n : ℕ) (x : ∀ n, M n), x ∈ L → (x n = 0 ↔ x ∈ I ^ (n + 1) • L)) := by
  classical
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M 0)
  choose g hg hg0 using fun i : Fin r => exists_forall_eq_of_surjective t ht 0 (s i)
  have h0 : Submodule.span R (Set.range fun i => g i 0) = ⊤ := by
    have : (fun i => g i 0) = s := funext hg0
    rw [this, hs]
  have hspan : ∀ n, Submodule.span R (Set.range fun i => g i n) = ⊤ :=
    span_range_apply_eq_top t I hI hker g hg h0
  let Φ : (Fin r → R) →ₗ[R] (∀ n, M n) := Fintype.linearCombination R g
  have hΦ : ∀ (c : Fin r → R) (k : ℕ), Φ c k = Ψ R g k c := by
    intro c k
    simp [Φ, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply]
  have hgL : ∀ i, g i ∈ L := fun i => (hL _).mpr (hg i)
  have hrange_le : LinearMap.range Φ ≤ L := by
    rw [Fintype.range_linearCombination, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hgL i
  have key : ∀ x ∈ L, ∀ (n : ℕ) (c₀ : Fin r → R), Ψ R g n c₀ = x n →
      ∃ c : Fin r → R, Φ c = x ∧ ∀ i, c i - c₀ i ∈ I ^ (n + 1) := by
    intro x hx n c₀ hc₀
    obtain ⟨c, hc, hcc₀⟩ :=
      exists_forall_Ψ_eq t I hI hker g hg hspan x ((hL x).mp hx) n c₀ hc₀
    exact ⟨c, funext fun k => by rw [hΦ, hc k], hcc₀⟩
  have hL_eq : L = LinearMap.range Φ := by
    refine le_antisymm (fun x hx => ?_) hrange_le
    obtain ⟨c₀, hc₀⟩ := Ψ_surjective g hspan 0 (x 0)
    obtain ⟨c, hc, -⟩ := key x hx 0 c₀ hc₀
    exact ⟨c, hc⟩
  refine ⟨?_, fun n y => ?_, fun n x hx => ⟨fun hxn => ?_, fun hxI => ?_⟩⟩
  · rw [hL_eq]; infer_instance
  · obtain ⟨x, hx, hxn⟩ := exists_forall_eq_of_surjective t ht n y
    exact ⟨x, (hL x).mpr hx, hxn⟩
  · obtain ⟨c, hc, hc0⟩ := key x hx n 0 (by simp [hxn])
    have hcmem : c ∈ I ^ (n + 1) • (⊤ : Submodule R (Fin r → R)) :=
      mem_smul_top_of_forall_apply_mem _ fun i => by simpa using hc0 i
    have : x ∈ (I ^ (n + 1) • (⊤ : Submodule R (Fin r → R))).map Φ := ⟨c, hcmem, hc⟩
    rw [Submodule.map_smul'', Submodule.map_top] at this
    exact smul_mono_right _ hrange_le this
  · have : x n ∈ (I ^ (n + 1) • L).map (LinearMap.proj n : (∀ k, M k) →ₗ[R] M n) :=
      Submodule.mem_map_of_mem hxI
    rw [Submodule.map_smul''] at this
    have hle : I ^ (n + 1) • L.map (LinearMap.proj n : (∀ k, M k) →ₗ[R] M n) ≤ ⊥ := by
      rw [← hI n]; exact smul_mono_right _ le_top
    simpa using hle this
end IsAdicComplete
