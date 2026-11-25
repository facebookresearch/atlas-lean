/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Multiset.Count
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

open scoped DirectSum

/-!
# Uniqueness of elementary divisors for finite abelian groups

This file ports the book lemma from `v1/Atlas/AlgebraNotes/code/AbelianGroups.lean`
("The multiplicities of the powers of `p` in the decomposition of `A_p` as a
product of cyclic groups are uniquely determined by `A`").

Correction to the v1 formalization: the v1 declaration
`AbelianGroups.torsion_subgroup_structure` states only the *existence* of a
decomposition of the torsion subgroup into cyclic groups (which is Mathlib's
`AddCommGroup.equiv_directSum_zmod_of_finite` for the finite torsion subgroup),
not the book's uniqueness claim, and the audit rates its faithfulness 1/5 for
that reason. This file proves the uniqueness claim itself: two decompositions
of the same finite abelian group into cyclic `p`-power groups have the same
number of factors and the same multiset of exponents.

## Main result

* `elementary_divisors_unique`: if `A` is additively equivalent to
  `⨁ i, ZMod (p ^ e i)` and to `⨁ i, ZMod (p ^ f i)` with all exponents
  positive, then the two index types have the same cardinality and the
  multisets of exponents agree.

The proof counts, for each `k`, the elements annihilated by `p ^ k`: in a
decomposition into cyclic `p`-power groups this count is
`∏ i, p ^ min (e i) k`, so the sums `∑ i, min (e i) k` are invariants, their
successive differences give the numbers of exponents `≥ k`, and those
determine the multiset of exponents. The positivity hypothesis is needed:
`ZMod 1` is trivial, so zero exponents are invisible to every such count.
-/

/-- The number of elements of `A` annihilated by `p ^ k`. -/
private noncomputable def torsionCard (A : Type*) [AddCommGroup A] (p k : ℕ) : ℕ :=
  Nat.card {x : A // (p ^ k : ℕ) • x = 0}

/-- The torsion count is invariant under additive equivalences. -/
private theorem torsionCard_congr {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (p k : ℕ) : torsionCard A p k = torsionCard B p k := by
  refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun x => ?_)
  show (p ^ k : ℕ) • x = 0 ↔ (p ^ k : ℕ) • e x = 0
  constructor
  · intro hx
    rw [← map_nsmul e (p ^ k) x, hx, map_zero]
  · intro hx
    have h : e ((p ^ k : ℕ) • x) = e 0 := by
      rw [map_nsmul, hx, map_zero]
    exact e.injective h

/-- The torsion count of a single cyclic `p`-power group. -/
private theorem torsionCard_zmod_pow (p : ℕ) (hp : 0 < p) (e k : ℕ) :
    Nat.card {x : ZMod (p ^ e) // (p ^ k : ℕ) • x = 0} = p ^ min e k := by
  classical
  have hne : NeZero (p ^ e) := ⟨pow_ne_zero _ (Nat.pos_iff_ne_zero.mp hp)⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- Transport the count to multiples below `p ^ e`.
  have hbij : (Finset.univ.filter (fun x : ZMod (p ^ e) => (p ^ k : ℕ) • x = 0)).card
      = ((Finset.range (p ^ e)).filter (fun v => p ^ e ∣ p ^ k * v)).card := by
    refine Finset.card_nbij (fun x => ZMod.val x) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, Finset.mem_range,
        true_and] at hx ⊢
      refine ⟨ZMod.val_lt x, ?_⟩
      have hx0 : (↑(p ^ k) : ZMod (p ^ e)) * x = 0 := by
        rwa [nsmul_eq_mul] at hx
      have hx0' : (↑(p ^ k * ZMod.val x) : ZMod (p ^ e)) = 0 := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val]
        exact hx0
      exact (ZMod.natCast_eq_zero_iff _ _).mp hx0'
    · intro x _ y _ hxy
      exact ZMod.val_injective _ hxy
    · intro v hv
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hv
      refine ⟨(v : ZMod (p ^ e)), ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [nsmul_eq_mul, ← Nat.cast_mul]
        exact (ZMod.natCast_eq_zero_iff _ _).mpr hv.2
      · exact ZMod.val_natCast_of_lt hv.1
  rw [hbij]
  -- Count the multiples.
  rcases lt_or_ge k e with hke | hke
  · -- The condition is equivalent to `p ^ (e - k) ∣ v`.
    have hcond : ∀ v : ℕ, p ^ e ∣ p ^ k * v ↔ p ^ (e - k) ∣ v := by
      intro v
      have hpow : p ^ e = p ^ k * p ^ (e - k) := by
        rw [← pow_add, Nat.add_sub_cancel' hke.le]
      rw [hpow, Nat.mul_dvd_mul_iff_left (pow_pos hp k)]
    rw [Finset.filter_congr (fun v _ => hcond v)]
    have hD : 0 < p ^ (e - k) := pow_pos hp _
    have hsplit : p ^ e = p ^ (e - k) * p ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hke.le]
    rw [hsplit, min_eq_right hke.le]
    conv_rhs => rw [← Finset.card_range (p ^ k)]
    refine Finset.card_nbij (fun v => v / p ^ (e - k)) ?_ ?_ ?_
    · intro v hv
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hv ⊢
      rw [Nat.div_lt_iff_lt_mul hD, mul_comm (p ^ k) (p ^ (e - k))]
      exact hv.1
    · intro v hv w hw hvw
      simp only [Finset.mem_coe, Finset.mem_filter] at hv hw
      have h1 : v = v / p ^ (e - k) * p ^ (e - k) := (Nat.div_mul_cancel hv.2).symm
      have h2 : w = w / p ^ (e - k) * p ^ (e - k) := (Nat.div_mul_cancel hw.2).symm
      have hvw' : v / p ^ (e - k) = w / p ^ (e - k) := hvw
      rw [h1, h2, hvw']
    · intro t ht
      simp only [Finset.mem_coe, Finset.mem_range] at ht
      refine ⟨t * p ^ (e - k), ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
        refine ⟨?_, dvd_mul_left _ _⟩
        rw [mul_comm (p ^ (e - k)) (p ^ k)]
        exact Nat.mul_lt_mul_of_pos_right ht hD
      · show (t * p ^ (e - k)) / p ^ (e - k) = t
        rw [mul_comm, Nat.mul_div_right _ hD]
  · -- Every `v` satisfies the condition.
    have hcond : ∀ v : ℕ, p ^ e ∣ p ^ k * v :=
      fun v => dvd_mul_of_dvd_left (pow_dvd_pow p hke) v
    rw [Finset.filter_true_of_mem (fun v _ => hcond v), Finset.card_range,
      min_eq_left hke]

/-- The torsion count of a direct sum of cyclic `p`-power groups. -/
private theorem torsionCard_directSum_zmod (p : ℕ) (hp : 0 < p) {ι : Type*} [Fintype ι]
    (e : ι → ℕ) (k : ℕ) :
    torsionCard (⨁ i, ZMod (p ^ e i)) p k = ∏ i, p ^ min (e i) k := by
  classical
  have hstep : Nat.card {x : ⨁ i, ZMod (p ^ e i) // (p ^ k : ℕ) • x = 0}
      = ∏ i, Nat.card {x : ZMod (p ^ e i) // (p ^ k : ℕ) • x = 0} := by
    calc Nat.card {x : ⨁ i, ZMod (p ^ e i) // (p ^ k : ℕ) • x = 0}
        = Nat.card {y : ∀ i, ZMod (p ^ e i) // ∀ i, (p ^ k : ℕ) • y i = 0} := by
          refine Nat.card_congr
            (Equiv.subtypeEquiv (DirectSum.addEquivProd _).toEquiv fun x => ?_)
          constructor
          · intro hx i
            have hcomp : ((p ^ k : ℕ) • x) i = 0 := by
              rw [hx]; exact DFinsupp.zero_apply i
            rw [DFinsupp.nsmul_apply] at hcomp
            exact hcomp
          · intro hx
            apply DFinsupp.ext
            intro i
            rw [DFinsupp.nsmul_apply, DFinsupp.zero_apply]
            exact hx i
      _ = Nat.card (∀ i, {x : ZMod (p ^ e i) // (p ^ k : ℕ) • x = 0}) :=
          Nat.card_congr
            (Equiv.subtypePiEquivPi
              (p := fun i (x : ZMod (p ^ e i)) => (p ^ k : ℕ) • x = 0))
      _ = ∏ i, Nat.card {x : ZMod (p ^ e i) // (p ^ k : ℕ) • x = 0} := Nat.card_pi
  unfold torsionCard
  rw [hstep]
  exact Finset.prod_congr rfl fun i _ => torsionCard_zmod_pow p hp (e i) k

/-- The successive differences of `∑ i, min (e i) k` count the exponents `≥ k`. -/
private theorem sum_min_eq_sum_min_add_filter_card {n : ℕ} (e : Fin n → ℕ) (k : ℕ)
    (hk : 1 ≤ k) :
    ∑ i, min (e i) k = ∑ i, min (e i) (k - 1) +
      (Finset.univ.filter (fun i => k ≤ e i)).card := by
  have hpoint : ∀ i : Fin n, min (e i) k = min (e i) (k - 1) + (if k ≤ e i then 1 else 0) := by
    intro i
    by_cases hke : k ≤ e i
    · simp only [hke, ite_true]
      rw [min_eq_right hke, min_eq_right (by omega : k - 1 ≤ e i)]
      omega
    · simp only [hke, ite_false]
      rw [min_eq_left (by omega : e i ≤ k), min_eq_left (by omega : e i ≤ k - 1),
        add_zero]
  calc ∑ i, min (e i) k
      = ∑ i, (min (e i) (k - 1) + (if k ≤ e i then 1 else 0)) :=
        Finset.sum_congr rfl fun i _ => hpoint i
    _ = (∑ i, min (e i) (k - 1)) + ∑ i, (if k ≤ e i then 1 else 0) :=
        Finset.sum_add_distrib
    _ = _ := by rw [Finset.sum_boole, Nat.cast_id]

/-- A multiset of naturals is determined by the numbers of elements `≥ k`. -/
private theorem multiset_eq_of_threshold_card {n m : ℕ} {e : Fin n → ℕ} {f : Fin m → ℕ}
    (he : ∀ i, 0 < e i) (hf : ∀ i, 0 < f i)
    (h : ∀ k : ℕ, 1 ≤ k → (Finset.univ.filter (fun i => k ≤ e i)).card =
      (Finset.univ.filter (fun j => k ≤ f j)).card) :
    Multiset.map e Finset.univ.val = Multiset.map f Finset.univ.val := by
  classical
  -- The threshold counts of the two multisets agree for `k ≥ 1`.
  have hthr : ∀ k : ℕ, 1 ≤ k →
      (Multiset.filter (fun x => k ≤ x) (Multiset.map e Finset.univ.val)).card =
        (Multiset.filter (fun x => k ≤ x) (Multiset.map f Finset.univ.val)).card := by
    intro k hk
    have hfilter : ∀ {n : ℕ} (g : Fin n → ℕ),
        Multiset.filter ((fun x => k ≤ x) ∘ g) Finset.univ.val
          = Multiset.filter (fun i => k ≤ g i) Finset.univ.val :=
      fun g => Multiset.filter_congr (fun x _ => Iff.rfl)
    have h1 : Multiset.filter (fun x => k ≤ x) (Multiset.map e Finset.univ.val)
        = Multiset.map e (Finset.univ.filter (fun i => k ≤ e i)).val := by
      rw [Multiset.filter_map, hfilter, Finset.filter_val]
    have h2 : Multiset.filter (fun x => k ≤ x) (Multiset.map f Finset.univ.val)
        = Multiset.map f (Finset.univ.filter (fun j => k ≤ f j)).val := by
      rw [Multiset.filter_map, hfilter, Finset.filter_val]
    rw [h1, h2, Multiset.card_map, Multiset.card_map]
    exact h k hk
  apply Multiset.ext.mpr
  intro a
  rcases eq_or_ne a 0 with rfl | ha0
  · -- No exponent is zero, so `0` occurs in neither multiset.
    have he0 : Multiset.count 0 (Multiset.map e Finset.univ.val) = 0 := by
      rw [Multiset.count_eq_zero]
      intro hmem
      rw [Multiset.mem_map] at hmem
      obtain ⟨i, -, hi⟩ := hmem
      exact (he i).ne' hi
    have hf0 : Multiset.count 0 (Multiset.map f Finset.univ.val) = 0 := by
      rw [Multiset.count_eq_zero]
      intro hmem
      rw [Multiset.mem_map] at hmem
      obtain ⟨j, -, hj⟩ := hmem
      exact (hf j).ne' hj
    rw [he0, hf0]
  · -- `count a = threshold(a) - threshold(a + 1)` for `a ≥ 1`.
    have key : ∀ {n : ℕ} (g : Fin n → ℕ),
        Multiset.count a (Multiset.map g Finset.univ.val) +
          (Multiset.filter (fun x => a + 1 ≤ x) (Multiset.map g Finset.univ.val)).card =
            (Multiset.filter (fun x => a ≤ x) (Multiset.map g Finset.univ.val)).card := by
      intro n g
      have hsplit := Multiset.filter_add_not (p := fun x => a = x)
        (s := Multiset.filter (fun x => a ≤ x) (Multiset.map g Finset.univ.val))
      simp only [Multiset.filter_filter] at hsplit
      have hleft : Multiset.filter (fun x => a = x ∧ a ≤ x)
          (Multiset.map g Finset.univ.val) =
          Multiset.filter (fun x => a = x) (Multiset.map g Finset.univ.val) := by
        apply Multiset.filter_congr
        intro x _
        constructor
        · exact fun hx => hx.1
        · intro hx
          exact ⟨hx, by omega⟩
      have hright : Multiset.filter (fun x => ¬a = x ∧ a ≤ x)
          (Multiset.map g Finset.univ.val) =
          Multiset.filter (fun x => a + 1 ≤ x) (Multiset.map g Finset.univ.val) := by
        apply Multiset.filter_congr
        intro x _
        constructor
        · rintro ⟨h1, h2⟩
          omega
        · intro h1
          exact ⟨by omega, by omega⟩
      rw [hleft, hright] at hsplit
      have hcard := congrArg Multiset.card hsplit
      rw [Multiset.card_add, ← Multiset.count_eq_card_filter_eq] at hcard
      exact hcard
    have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
    have h1 := key e
    have h2 := key f
    rw [hthr a ha1, hthr (a + 1) (by omega)] at h1
    rw [← h1] at h2
    exact (Nat.add_right_cancel h2).symm

/-- **Uniqueness of elementary divisors.** Let $p$ be a prime and let $A$ be an abelian group.
If $A \cong \bigoplus_{i=1}^{n} \mathbb{Z}/p^{e_i}\mathbb{Z}$ and
$A \cong \bigoplus_{j=1}^{m} \mathbb{Z}/p^{f_j}\mathbb{Z}$ for positive integers
$e_1, \dots, e_n$ and $f_1, \dots, f_m$, then $n = m$ and the multisets
$\{e_1, \dots, e_n\}$ and $\{f_1, \dots, f_m\}$ are equal. -/
theorem elementary_divisors_unique {p : ℕ} (hp : p.Prime) {n m : ℕ}
    {e : Fin n → ℕ} {f : Fin m → ℕ} (he : ∀ i, 0 < e i) (hf : ∀ i, 0 < f i)
    {A : Type*} [AddCommGroup A]
    (hA : Nonempty (A ≃+ ⨁ i, ZMod (p ^ e i)))
    (hB : Nonempty (A ≃+ ⨁ i, ZMod (p ^ f i))) :
    n = m ∧ Multiset.map e Finset.univ.val = Multiset.map f Finset.univ.val := by
  classical
  obtain ⟨eA⟩ := hA
  obtain ⟨eB⟩ := hB
  -- The torsion counts of the two decompositions agree for every `k`.
  have hcount : ∀ k : ℕ, ∏ i, p ^ min (e i) k = ∏ i, p ^ min (f i) k := by
    intro k
    have h1 := torsionCard_directSum_zmod p hp.pos e k
    have h2 := torsionCard_directSum_zmod p hp.pos f k
    have h3 := torsionCard_congr eA p k
    have h4 := torsionCard_congr eB p k
    rw [← h1, ← h2, ← h3, ← h4]
  -- Hence the sums of truncated exponents agree.
  have hsum : ∀ k : ℕ, ∑ i, min (e i) k = ∑ i, min (f i) k := by
    intro k
    have h := hcount k
    rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum] at h
    exact Nat.pow_right_injective hp.two_le h
  -- Hence the threshold counts agree for `k ≥ 1`.
  have hthr : ∀ k : ℕ, 1 ≤ k → (Finset.univ.filter (fun i => k ≤ e i)).card =
      (Finset.univ.filter (fun j => k ≤ f j)).card := by
    intro k hk
    have h1 := sum_min_eq_sum_min_add_filter_card e k hk
    have h2 := sum_min_eq_sum_min_add_filter_card f k hk
    have hs1 := hsum k
    have hs2 := hsum (k - 1)
    omega
  have hmulti := multiset_eq_of_threshold_card he hf hthr
  refine ⟨?_, hmulti⟩
  have hcard : n = m := by
    have h2 := congrArg Multiset.card hmulti
    simpa using h2
  exact hcard
