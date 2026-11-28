/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination
import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity

/-!
# The normal covering number of the symmetric groups

We refute the eventual form of the Bubboloni–Praeger–Spiga normal covering conjecture
(Kourovka Notebook Problem 18.23). The counterexamples use a fixed product of ten primes
and an unbounded family of multiples of that product.
-/

namespace MathlibExt.GroupTheory.NormalCoveringSymmetricKourovka18Problem23Wanted

@[expose] public section

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.23 (D.
Bubboloni, C. E. Praeger, P. Spiga). UnsolvedMath record UM-00701452 (`KOU-18.23`), dataset
ulamai/UnsolvedMath v1.8.0.

The conjectured value is `(n/2)(1 - 1/p₁)` (`r = 1`, `α₁ = 1`), `(n/2)(1 - 1/p₁) + 1` (`r = 1`, `α₁
≥ 2`), `(n/2)(1 - 1/p₁)(1 - 1/p₂) + 1` (`r = 2`, `α₁ + α₂ = 2`) and `(n/2)(1 - 1/p₁)(1 - 1/p₂) + 2`
(`r ≥ 2`, `α₁ + ⋯ + α_r ≥ 3`), computed in `ℚ`. The target is the "for `n` sufficiently large" form;
its refutation also refutes the conjecture for all `n` and avoids small degrees where the formula is
not meant (for `n = 3` it gives `1`, while no finite group is covered by the conjugates of one
proper subgroup).
-/

/-- **Normal covering number of the symmetric group.** For a natural number $n$, the normal
covering number $\gamma(S_n)$ is the least $k$ for which there are proper subgroups
$H_1, \dots, H_k$ of the symmetric group $S_n$ such that every element of $S_n$ is conjugate to an
element of some $H_i$. When no such subgroups exist, as for $n \le 2$, it is $0$. -/
noncomputable def normalCoveringNumber (n : ℕ) : ℕ :=
  sInf {k | ∃ H : Fin k → Subgroup (Equiv.Perm (Fin n)), (∀ i, H i ≠ ⊤) ∧
    ∀ σ : Equiv.Perm (Fin n), ∃ i, ∃ τ ∈ H i, IsConj σ τ}

/-- **Bubboloni–Praeger–Spiga conjectured value.** For a natural number $n \ge 2$, write
$n = p_1^{\alpha_1} \cdots p_r^{\alpha_r}$ with primes $p_1 < \cdots < p_r$ and exponents
$\alpha_i \ge 1$, and let $p_2$ be the least prime factor of $n / p_1^{\alpha_1}$. The conjectured
value of $n$ is the rational number $\frac{n}{2}(1 - \frac{1}{p_1})$ if $r = 1$ and $\alpha_1 = 1$;
$\frac{n}{2}(1 - \frac{1}{p_1}) + 1$ if $r = 1$ and $\alpha_1 \ge 2$;
$\frac{n}{2}(1 - \frac{1}{p_1})(1 - \frac{1}{p_2}) + 1$ if $r = 2$ and $\alpha_1 = \alpha_2 = 1$;
and $\frac{n}{2}(1 - \frac{1}{p_1})(1 - \frac{1}{p_2}) + 2$ if $r \ge 2$ and
$\alpha_1 + \cdots + \alpha_r \ge 3$. For $n = 0$ and $n = 1$ the value is $2$. -/
def conjecturedValue (n : ℕ) : ℚ :=
  let p₁ := n.minFac
  let p₂ := (n / p₁ ^ n.factorization p₁).minFac
  let a : ℚ := n / 2 * (1 - 1 / (p₁ : ℚ))
  let b : ℚ := a * (1 - 1 / (p₂ : ℚ))
  if n.primeFactors.card = 1 then
    (if n.primeFactorsList.length = 1 then a else a + 1)
  else if n.primeFactorsList.length = 2 then b + 1 else b + 2

/-- **Bubboloni–Praeger–Spiga normal covering conjecture (eventual form).** There is a natural
number $N$ such that, for every $n \ge N$, the normal covering number $\gamma(S_n)$ of the
symmetric group $S_n$ equals the Bubboloni–Praeger–Spiga conjectured value of $n$.

This is Kourovka Problem 18.23 (D. Bubboloni, C. E. Praeger, P. Spiga) in the form "for all
sufficiently large $n$" that the proposers single out. -/
def normalCoveringNumberEventuallyConjectured : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, (normalCoveringNumber n : ℚ) = conjecturedValue n

end

open Equiv Equiv.Perm Finset MulAction
open scoped Pointwise

private theorem normalCoveringNumber_le_of_family {n : ℕ} {ι : Type} [Fintype ι]
    (H : ι → Subgroup (Perm (Fin n))) (hH : ∀ i, H i ≠ ⊤)
    (hcover : ∀ σ, ∃ i, ∃ τ ∈ H i, IsConj σ τ) :
    normalCoveringNumber n ≤ Fintype.card ι := by
  classical
  let e := Fintype.equivFin ι
  apply Nat.sInf_le
  refine ⟨H ∘ e.symm, fun i ↦ hH (e.symm i), fun σ ↦ ?_⟩
  obtain ⟨i, τ, hτ, hc⟩ := hcover σ
  exact ⟨e i, τ, by simpa [e] using hτ, hc⟩

private def initialSegment {k n : ℕ} (hk : k ≤ n) : Finset (Fin n) :=
  univ.map (Fin.castLEEmb hk)

private theorem card_initialSegment {k n : ℕ} (hk : k ≤ n) :
    (initialSegment hk).card = k := by
  simp [initialSegment]

private theorem mem_initialSegment {k n : ℕ} (hk : k ≤ n) (x : Fin n) :
    x ∈ initialSegment hk ↔ x.val < k := by
  simp only [initialSegment, mem_map, mem_univ, true_and]
  constructor
  · rintro ⟨a, rfl⟩
    exact a.isLt
  · intro h
    exact ⟨⟨x, h⟩, Fin.ext rfl⟩

private theorem stabilizer_initialSegment_ne_top {k n : ℕ} (hk : 0 < k) (hkn : k < n) :
    stabilizer (Perm (Fin n)) (initialSegment hkn.le : Set (Fin n)) ≠ ⊤ := by
  let x : Fin n := ⟨0, hk.trans hkn⟩
  let y : Fin n := ⟨k, hkn⟩
  intro h
  have hx : x ∈ (initialSegment hkn.le : Set (Fin n)) := (mem_initialSegment _ _).2 hk
  have hxy : swap x y ∈ stabilizer (Perm (Fin n))
      (initialSegment hkn.le : Set (Fin n)) := h ▸ Subgroup.mem_top _
  rw [Equiv.swap_mem_stabilizer] at hxy
  exact (Nat.lt_irrefl k) ((mem_initialSegment _ y).1 (hxy.mp hx))

private theorem conjugate_mem_stabilizer_initialSegment {k n : ℕ} (hk : k ≤ n)
    (σ : Perm (Fin n)) (s : Finset (Fin n)) (hs : s.card = k)
    (hσ : σ ∈ stabilizer (Perm (Fin n)) (s : Set (Fin n))) :
    ∃ τ ∈ stabilizer (Perm (Fin n)) (initialSegment hk : Set (Fin n)), IsConj σ τ := by
  let a : Set.powersetCard (Fin n) k := ⟨s, hs⟩
  let b : Set.powersetCard (Fin n) k := ⟨initialSegment hk, card_initialSegment hk⟩
  let := Set.powersetCard.isPretransitive (α := Fin n) (n := k)
  obtain ⟨g, hg⟩ := exists_smul_eq (Perm (Fin n)) a b
  let φ := stabilizerEquivStabilizer hg.symm
  have hσ' : σ ∈ stabilizer (Perm (Fin n)) a := by
    rw [Set.powersetCard.stabilizer_coe]
    exact hσ
  refine ⟨φ ⟨σ, hσ'⟩, ?_, ?_⟩
  · change (φ ⟨σ, hσ'⟩ : Perm (Fin n)) ∈ stabilizer _ (b : Set (Fin n))
    rw [← Set.powersetCard.stabilizer_coe]
    exact (φ ⟨σ, hσ'⟩).property
  · exact isConj_iff.mpr ⟨g, (stabilizerEquivStabilizer_apply hg.symm ⟨σ, hσ'⟩).symm⟩

private theorem exists_commuting_pow_eq_one_of_dvd_cycleType
    {α : Type*} [Fintype α] [DecidableEq α] {p : ℕ} (hp : 1 < p) (σ : Perm α)
    (hσ : ∀ k ∈ σ.cycleType, p ∣ k) :
    ∃ ρ : Perm α, Commute σ ρ ∧ ρ ^ p = 1 ∧ ρ.support = σ.support := by
  induction σ using Equiv.Perm.cycle_induction_on with
  | base_one => exact ⟨1, Commute.one_right _, one_pow _, rfl⟩
  | base_cycles σ hcycle =>
    obtain ⟨k, hk⟩ : p ∣ orderOf σ := by
      apply hσ
      simp [hcycle.cycleType, hcycle.orderOf]
    have horder := orderOf_pos σ
    have hk₀ : 0 < k :=
      Nat.pos_of_ne_zero fun h ↦ horder.ne' (by simpa only [h, mul_zero] using hk)
    refine ⟨σ ^ k, (Commute.refl σ).pow_right k, ?_, ?_⟩
    · rw [← pow_mul, mul_comm k p, ← hk, pow_orderOf_eq_one]
    · apply hcycle.support_pow_of_pos_of_lt_orderOf hk₀
      rw [hk]
      simpa using Nat.mul_lt_mul_of_pos_right hp hk₀
  | induction_disjoint σ τ hd _ ihσ ihτ =>
    rw [hd.cycleType_mul] at hσ
    obtain ⟨ρ, hcρ, hpρ, hsρ⟩ := ihσ fun k hk ↦ hσ k (Multiset.mem_add.mpr (Or.inl hk))
    obtain ⟨η, hcη, hpη, hsη⟩ := ihτ fun k hk ↦ hσ k (Multiset.mem_add.mpr (Or.inr hk))
    have hd' := Equiv.Perm.disjoint_iff_disjoint_support.mp hd
    have hση : Disjoint σ η := by rwa [Equiv.Perm.disjoint_iff_disjoint_support, hsη]
    have hρτ : Disjoint ρ τ := by rwa [Equiv.Perm.disjoint_iff_disjoint_support, hsρ]
    have hρη : Disjoint ρ η := by rwa [Equiv.Perm.disjoint_iff_disjoint_support, hsρ, hsη]
    refine ⟨ρ * η, (hcρ.mul_right hση.commute).mul_left
      (hρτ.commute.symm.mul_right hcη), ?_, ?_⟩
    · rw [hρη.commute.mul_pow, hpρ, hpη, mul_one]
    · rw [hρη.support_mul, hd.support_mul, hsρ, hsη]

private theorem cycleType_of_pow_eq_one_of_support_eq_univ {n p : ℕ}
    [Fact p.Prime] {ρ : Perm (Fin n)} (hp : ρ ^ p = 1) (hρ : ρ.support = univ) :
    ρ.cycleType = Multiset.replicate (n / p) p := by
  have htype := cycleType_of_pow_prime_eq_one hp
  have hsum := ρ.sum_cycleType
  rw [hρ, card_univ, Fintype.card_fin, htype, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id] at hsum
  have hcard : ρ.cycleType.card = n / p := by
    simpa only [Nat.mul_div_cancel _ (Fact.out : p.Prime).pos] using congrArg (· / p) hsum
  exact htype.trans (congrArg (Multiset.replicate · p) hcard)

private theorem exists_with_uniform_cycleType (n : ℕ) {p : ℕ} (hp : 1 < p) (hpn : p ∣ n) :
    ∃ ρ : Perm (Fin n), ρ.cycleType = Multiset.replicate (n / p) p := by
  rw [Equiv.Perm.exists_with_cycleType_iff]
  constructor
  · simpa [Multiset.sum_replicate, nsmul_eq_mul] using (Nat.div_mul_cancel hpn).le
  · intro a ha
    obtain rfl := Multiset.eq_of_mem_replicate ha
    omega

private theorem centralizer_ne_top_of_uniform_cycleType {n p : ℕ} (hn : 3 ≤ n)
    (hpn : p ∣ n) {ρ : Perm (Fin n)}
    (hρ : ρ.cycleType = Multiset.replicate (n / p) p) :
    Subgroup.centralizer ({ρ} : Set (Perm (Fin n))) ≠ ⊤ := by
  have hs : ρ.support = univ := by
    apply eq_univ_of_card
    rw [← ρ.sum_cycleType, hρ, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id,
      Nat.div_mul_cancel hpn, Fintype.card_fin]
  let x : Fin n := ⟨0, by omega⟩
  have hx : ρ x ≠ x := mem_support.mp (hs ▸ mem_univ x)
  obtain ⟨z, hz⟩ : ∃ z, z ∉ ({x, ρ x} : Finset (Fin n)) := by
    by_contra! h
    have hc := Finset.card_insert_le (a := x) ({ρ x} : Finset (Fin n))
    rw [eq_univ_of_forall h, card_univ, Fintype.card_fin, card_singleton] at hc
    omega
  have hzx : z ≠ x := fun h ↦ hz (by simp [h])
  have hzρ : z ≠ ρ x := fun h ↦ hz (by simp [h])
  intro h
  have hc : swap (ρ x) z ∈ Subgroup.centralizer ({ρ} : Set (Perm (Fin n))) :=
    h ▸ Subgroup.mem_top _
  have he := DFunLike.congr_fun (Subgroup.mem_centralizer_singleton_iff.mp hc) x
  exact hzρ (by simpa [Perm.mul_apply, swap_apply_of_ne_of_ne hx.symm hzx.symm] using he)

private theorem conjugate_mem_centralizer_of_dvd_cycleType {n p : ℕ} (hp : p.Prime)
    {ρ σ : Perm (Fin n)} (hρ : ρ.cycleType = Multiset.replicate (n / p) p)
    (hσ : σ.support = univ) (hdiv : ∀ k ∈ σ.cycleType, p ∣ k) :
    ∃ τ ∈ Subgroup.centralizer ({ρ} : Set (Perm (Fin n))), IsConj σ τ := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨η, hc, hη, hs⟩ := exists_commuting_pow_eq_one_of_dvd_cycleType hp.one_lt σ hdiv
  have htype := cycleType_of_pow_eq_one_of_support_eq_univ hη (hs.trans hσ)
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr (htype.trans hρ.symm))
  refine ⟨g * σ * g⁻¹, Subgroup.mem_centralizer_singleton_iff.mpr ?_, isConj_iff.mpr ⟨g, rfl⟩⟩
  rw [← hg]
  exact hc.map (MulAut.conj g).toMonoidHom

private def coveringSizes (n m : ℕ) : Finset ℕ :=
  Icc 1 (n / 3) ∪ ((Ioc (n / 3) (n / 2)).filter (m.Coprime ·))

private theorem mem_coveringSizes_of_small {n m k : ℕ} (hk : 0 < k) (hkn : k ≤ n / 3) :
    k ∈ coveringSizes n m :=
  mem_union_left _ (mem_Icc.mpr ⟨hk, hkn⟩)

private theorem mem_coveringSizes_of_coprime {n m k : ℕ} (hk : 0 < k) (hkn : k ≤ n / 2)
    (hcop : m.Coprime k) : k ∈ coveringSizes n m := by
  by_cases h : k ≤ n / 3
  · exact mem_coveringSizes_of_small hk h
  · exact mem_union_right _ (mem_filter.mpr ⟨mem_Ioc.mpr ⟨lt_of_not_ge h, hkn⟩, hcop⟩)

private theorem coveringSizes_bounds {n m k : ℕ} (hk : k ∈ coveringSizes n m) :
    0 < k ∧ k < n := by
  simp only [coveringSizes, mem_union, mem_Icc, mem_filter, mem_Ioc] at hk
  rcases hk with ⟨h₁, h₂⟩ | ⟨⟨h₁, h₂⟩, _⟩ <;> omega

private theorem covering_cases {n m : ℕ} (hm : 1 < m) (hmn : m ∣ n) (hn : 3 ≤ n)
    {l : List ℕ} (hsum : l.sum = n) (hpos : ∀ k ∈ l, 0 < k) :
    (∃ k ∈ l, k ∈ coveringSizes n m) ∨
    (∃ p ∈ m.primeFactors, ∀ k ∈ l, p ∣ k) := by
  match l with
  | [] => simp at hsum; omega
  | [a] =>
    obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm.ne'
    refine Or.inr ⟨p, hp.mem_primeFactors hpm (by omega), ?_⟩
    have ha : a = n := by simpa using hsum
    simpa [ha] using hpm.trans hmn
  | [a, b] =>
    have hab : a + b = n := by simpa using hsum
    let k := min a b
    have hkl : k ∈ [a, b] := by
      rcases le_total a b with hab | hba
      · simp [k, min_eq_left hab]
      · simp [k, min_eq_right hba]
    by_cases hcop : m.Coprime k
    · have hk := hpos k hkl
      have hkn : k ≤ n / 2 := by dsimp [k]; omega
      exact Or.inl ⟨k, hkl, mem_coveringSizes_of_coprime hk hkn hcop⟩
    · obtain ⟨p, hp, hgcd⟩ := Nat.exists_prime_and_dvd (mt Nat.coprime_iff_gcd_eq_one.mpr hcop)
      have hpm := hgcd.trans (Nat.gcd_dvd_left m k)
      have hpk := hgcd.trans (Nat.gcd_dvd_right m k)
      have hpn : p ∣ a + b := hab ▸ hpm.trans hmn
      refine Or.inr ⟨p, hp.mem_primeFactors hpm (by omega), ?_⟩
      rcases le_total a b with hab | hba
      · rw [show k = a from min_eq_left hab] at hpk
        have hpb : p ∣ b := (Nat.dvd_add_iff_right hpk).mpr hpn
        simpa using And.intro hpk hpb
      · rw [show k = b from min_eq_right hba] at hpk
        have hpa : p ∣ a := (Nat.dvd_add_iff_left hpk).mpr hpn
        simpa using And.intro hpa hpk
  | a :: b :: c :: l =>
    have hsmall : a ≤ n / 3 ∨ b ≤ n / 3 ∨ c ≤ n / 3 := by
      simp only [List.sum_cons] at hsum
      omega
    rcases hsmall with ha | hb | hc
    · exact Or.inl ⟨a, by simp, mem_coveringSizes_of_small (hpos a (by simp)) ha⟩
    · exact Or.inl ⟨b, by simp, mem_coveringSizes_of_small (hpos b (by simp)) hb⟩
    · exact Or.inl ⟨c, by simp, mem_coveringSizes_of_small (hpos c (by simp)) hc⟩

/-- A covering obtained from Maróti's construction by using the primes of a fixed divisor.
The centralizer of a permutation with all cycles of length `p` provides the subgroup for `p`. -/
private theorem normalCoveringNumber_le_coveringSizes {n m : ℕ} (hn : 3 ≤ n)
    (hm : 1 < m) (hmn : m ∣ n) :
    normalCoveringNumber n ≤ (coveringSizes n m).card + m.primeFactors.card := by
  classical
  have hpn (p : m.primeFactors) : p.val ∣ n := (Nat.dvd_of_mem_primeFactors p.prop).trans hmn
  have hprime (p : m.primeFactors) : p.val.Prime := Nat.prime_of_mem_primeFactors p.prop
  choose ρ hρ using fun p : m.primeFactors ↦
    exists_with_uniform_cycleType n (hprime p).one_lt (hpn p)
  let H : coveringSizes n m ⊕ m.primeFactors → Subgroup (Perm (Fin n)) :=
    Sum.elim (fun k ↦ stabilizer _ (initialSegment (coveringSizes_bounds k.prop).2.le :
        Set (Fin n))) (fun p ↦ Subgroup.centralizer {ρ p})
  have hH (i : coveringSizes n m ⊕ m.primeFactors) : H i ≠ ⊤ := by
    rcases i with k | p
    · obtain ⟨hk, hkn⟩ := coveringSizes_bounds k.prop
      exact stabilizer_initialSegment_ne_top hk hkn
    · exact centralizer_ne_top_of_uniform_cycleType hn (hpn p) (hρ p)
  suffices hcover : ∀ σ, ∃ i, ∃ τ ∈ H i, IsConj σ τ by
    simpa only [Fintype.card_sum, Fintype.card_coe] using normalCoveringNumber_le_of_family H hH
      hcover
  intro σ
  have hintrans (k : coveringSizes n m) (s : Finset (Fin n)) (hs : s.card = k.val)
      (hσ : σ ∈ stabilizer (Perm (Fin n)) (s : Set (Fin n))) :
      ∃ i, ∃ τ ∈ H i, IsConj σ τ := by
    obtain ⟨τ, hτ, hc⟩ := conjugate_mem_stabilizer_initialSegment
      (coveringSizes_bounds k.prop).2.le σ s hs hσ
    exact ⟨Sum.inl k, τ, hτ, hc⟩
  by_cases hσ : σ.support = univ
  · have hsum : σ.cycleType.toList.sum = n := by
      simp [σ.sum_cycleType, hσ]
    have hpos (k : ℕ) (hk : k ∈ σ.cycleType.toList) : 0 < k :=
      zero_lt_one.trans (one_lt_of_mem_cycleType (Multiset.mem_toList.mp hk))
    rcases covering_cases hm hmn hn hsum hpos with ⟨k, hk, hks⟩ | ⟨p, hp, hd⟩
    · obtain ⟨c, τ, hστ, hct, _, hcard⟩ := mem_cycleType_iff.mp (Multiset.mem_toList.mp hk)
      apply hintrans ⟨k, hks⟩ c.support hcard
      apply mem_stabilizer_set.mpr
      exact mem_support_iff_of_commute (hστ ▸ ((Commute.refl c).mul_right hct.commute).symm)
    · let p' : m.primeFactors := ⟨p, hp⟩
      obtain ⟨τ, hτ, hc⟩ := conjugate_mem_centralizer_of_dvd_cycleType (hprime p') (hρ p')
        hσ (fun k hk ↦ hd k (Multiset.mem_toList.mpr hk))
      exact ⟨Sum.inr p', τ, hτ, hc⟩
  · obtain ⟨x, hx⟩ : ∃ x, x ∉ σ.support := by
      simpa [eq_univ_iff_forall] using hσ
    apply hintrans ⟨1, mem_coveringSizes_of_small Nat.one_pos (by omega)⟩ {x} (by simp)
    apply mem_stabilizer_set.mpr
    have he := notMem_support.mp hx
    intro y
    simp only [coe_singleton, Set.mem_singleton_iff]
    exact (congrArg (σ y = ·) he.symm).to_iff.trans σ.injective.eq_iff

-- Only the interval above `n / 3` requires a count of numbers coprime to `m`.
private theorem card_coveringSizes_le {n m a : ℕ} (hm : 0 < m) (hn : n = m * (6 * a + 1)) :
    (coveringSizes n m).card ≤ n / 3 + m.totient * (a + 2) := by
  rw [coveringSizes]
  refine (card_union_le _ _).trans (add_le_add ?_ ?_)
  · simp
  have he : n = 6 * (m * a) + m := by rw [hn]; ring
  have he' : 2 * (m * a) + m * (a + 1) = 3 * (m * a) + m := by ring
  have hsub : Ioc (n / 3) (n / 2) ⊆ Ico (2 * (m * a)) (2 * (m * a) + m * (a + 1)) := by
    intro k hk
    rw [mem_Ioc] at hk
    rw [mem_Ico, he']
    omega
  refine (card_le_card (filter_subset_filter _ hsub)).trans ?_
  simpa [Nat.mul_div_cancel_left _ hm, add_assoc] using
    Nat.Ico_filter_coprime_le (2 * (m * a)) (m * (a + 1)) hm.ne'

-- These primes keep both least prime factors large and give a small enough totient ratio.
private def counterexamplePrimes : Finset ℕ := {43, 47, 53, 59, 61, 67, 71, 73, 79, 83}

private def modulus : ℕ :=
  ∏ p ∈ counterexamplePrimes, p

private theorem primeFactors_modulus : modulus.primeFactors = counterexamplePrimes := by
  apply Nat.primeFactors_prod
  have h : ∀ p : counterexamplePrimes, p.val.Prime := by decide
  exact fun p hp ↦ h ⟨p, hp⟩

private theorem modulus_value : modulus = 877779077635511999 := by
  norm_num [modulus, counterexamplePrimes, Finset.prod_insert]

private theorem totient_modulus : modulus.totient = 743828195587276800 := by
  rw [Nat.totient_eq_div_primeFactors_mul, primeFactors_modulus]
  change (modulus / modulus) * _ = _
  have hm : 0 < modulus := by rw [modulus_value]; decide
  rw [Nat.div_self hm, one_mul]
  norm_num [counterexamplePrimes, Finset.prod_insert]

private theorem conjecturedValue_lower_bound {n : ℕ} (hn : 3 ≤ n) (hmn : modulus ∣ n)
    (hprime : ∀ p, p.Prime → p ∣ n → 43 ≤ p) :
    (882 / 1849 : ℚ) * n + 2 ≤ conjecturedValue n := by
  have hsubset : modulus.primeFactors ⊆ n.primeFactors :=
    Nat.primeFactors_mono hmn (by omega)
  have hcard : 3 ≤ n.primeFactors.card := by
    refine le_trans ?_ (card_le_card hsubset)
    rw [primeFactors_modulus]
    decide
  have hlength : 3 ≤ n.primeFactorsList.length := by
    exact hcard.trans (Nat.toFinset_factors n ▸ List.toFinset_card_le _)
  have h43 : 43 ∣ n := Nat.dvd_of_mem_primeFactors (hsubset (by rw [primeFactors_modulus]; decide))
  have h47 : 47 ∣ n := Nat.dvd_of_mem_primeFactors (hsubset (by rw [primeFactors_modulus]; decide))
  have hmin : n.minFac = 43 := le_antisymm (Nat.minFac_le_of_dvd (by decide) h43)
    (hprime _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd _))
  let q := n / 43 ^ n.factorization 43
  have hq : 47 ∣ q := Nat.dvd_ordCompl_of_dvd_not_dvd h47 (by decide : ¬ 43 ∣ 47)
  have hqmin : 43 ≤ q.minFac := by
    have hq₁ : q ≠ 1 := fun h ↦ by rw [h] at hq; omega
    exact hprime _ (Nat.minFac_prime hq₁) ((Nat.minFac_dvd q).trans (Nat.ordCompl_dvd n 43))
  have hqminQ : (43 : ℚ) ≤ (q.minFac : ℚ) := by exact_mod_cast hqmin
  have hinv : (1 : ℚ) / q.minFac ≤ 1 / 43 :=
    one_div_le_one_div_of_le (by norm_num) hqminQ
  rw [conjecturedValue, hmin, ite_eq_right (by omega : n.primeFactors.card ≠ 1),
    ite_eq_right (by omega : n.primeFactorsList.length ≠ 2)]
  calc
    _ = (n / 2 : ℚ) * (1 - 1 / 43) * (1 - 1 / 43) + 2 := by ring
    _ ≤ _ := by
      change _ ≤ (n / 2 : ℚ) * (1 - 1 / 43) * (1 - 1 / (q.minFac : ℚ)) + 2
      refine add_le_add ?_ le_rfl
      exact mul_le_mul_of_nonneg_left (sub_le_sub_left hinv 1) (by positivity)

private theorem exists_counterexample (N : ℕ) :
    ∃ n ≥ N, (normalCoveringNumber n : ℚ) < conjecturedValue n := by
  -- The factorial keeps every prime below 43 out of the multiplier `6 * a + 1`.
  let a := (42 : ℕ).factorial * (N + 1000)
  let n := modulus * (6 * a + 1)
  have hm : 1 < modulus := by rw [modulus_value]; decide
  have ha : N + 1000 ≤ a := Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
  have hna : a ≤ n := by
    have h := Nat.le_mul_of_pos_left (6 * a + 1) (zero_lt_one.trans hm)
    omega
  have hn : 3 ≤ n := by omega
  have hmn : modulus ∣ n := dvd_mul_right _ _
  have hprime (p : ℕ) (hp : p.Prime) (hpn : p ∣ n) : 43 ≤ p := by
    rcases hp.dvd_mul.mp hpn with hpm | hpa
    · have hmem : p ∈ counterexamplePrimes := by
        rw [← primeFactors_modulus]
        exact hp.mem_primeFactors hpm (by omega)
      have h : ∀ p : counterexamplePrimes, 43 ≤ p.val := by decide
      exact h ⟨p, hmem⟩
    · by_contra! h
      have hpd : p ∣ Nat.factorial 42 := Nat.dvd_factorial hp.pos (by omega)
      have hpa' : p ∣ 6 * a := dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hpd _) _
      have hp₁ : p ∣ 1 := (Nat.dvd_add_iff_right hpa').mpr hpa
      exact hp.not_dvd_one hp₁
  have hupper := (normalCoveringNumber_le_coveringSizes hn hm hmn).trans
    (add_le_add (card_coveringSizes_le (zero_lt_one.trans hm) (a := a) rfl) le_rfl)
  have hcast : (normalCoveringNumber n : ℚ) ≤
      (↑(n / 3) : ℚ) + (modulus.totient : ℚ) * ((a : ℚ) + 2) +
        (modulus.primeFactors.card : ℚ) := by
    exact_mod_cast hupper
  have hdiv : (↑(n / 3) : ℚ) ≤ (n : ℚ) / 3 := by
    apply (le_div_iff₀ (by norm_num)).mpr
    exact_mod_cast Nat.div_mul_le_self n 3
  have hcard : modulus.primeFactors.card = 10 := by rw [primeFactors_modulus]; decide
  refine ⟨n, by omega, ?_⟩
  calc
    _ ≤ (n : ℚ) / 3 + (modulus.totient : ℚ) * ((a : ℚ) + 2) + 10 := by
      rw [hcard, Nat.cast_ofNat] at hcast
      exact hcast.trans (add_le_add (add_le_add hdiv le_rfl) le_rfl)
    _ < (882 / 1849 : ℚ) * n + 2 := by
      have haQ : (1000 : ℚ) ≤ a := by exact_mod_cast (show 1000 ≤ a by omega)
      have hnQ : (n : ℚ) = (877779077635511999 : ℚ) * (6 * (a : ℚ) + 1) := by
        exact_mod_cast (show n = 877779077635511999 * (6 * a + 1) by simp [n, modulus_value])
      rw [hnQ, totient_modulus, Nat.cast_ofNat]
      linarith only [haQ]
    _ ≤ _ := conjecturedValue_lower_bound hn hmn hprime

/--
**Refutation of the Bubboloni–Praeger–Spiga normal covering conjecture.** It is not the case
that there is a natural number $N$ such that, for every $n \ge N$, the normal covering number
$\gamma(S_n)$ of the symmetric group $S_n$ equals the Bubboloni–Praeger–Spiga conjectured value
of $n$. In other words, the conjecture fails for arbitrarily large $n$.

The Kourovka Archive records that A. Maróti showed the conjecture incorrect for odd $n$. His
covering, given in Section 2 of Bubboloni–Praeger–Spiga (2020), yields
$\gamma(S_n) \le n/3 + \varphi(n)/2 + \omega(n)$, where $\varphi$ is Euler's function and
$\omega(n)$ the number of distinct prime factors of $n$. This is below the conjectured value when
$n$ is the product of $r$ consecutive primes starting at a prime $p \ge 43$ and $r$ is large.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 18.23 (D. Bubboloni, C. E. Praeger, P. Spiga); resolution: D. Bubboloni, C.
E. Praeger and P. Spiga, Linear bounds for the normal covering number of the symmetric and
alternating groups, Monatsh. Math. 191 (2020), 229-247, Section 2, A. Maróti's construction: for n =
N(r, p), the product of r consecutive primes starting at p ≥ 43, and r ≥ r*, γ(Sym(n)) < (n/2)(1 -
1/p₁)(1 - 1/p₂) + 2, contradicting the conjecture for infinitely many p and r; Kourovka Archive,
Problem 18.23,
https://api.research-repository.uwa.edu.au/ws/files/49055019/Bubboloni_et_al_2019_Linear_bounds_for_the_normal_covering.pdf.
-/
public theorem normalCoveringNumberEventuallyConjectured_refuted :
    ¬ normalCoveringNumberEventuallyConjectured := by
  rintro ⟨N, hN⟩
  obtain ⟨n, hn, hlt⟩ := exists_counterexample N
  exact hlt.ne (hN n hn)

end MathlibExt.GroupTheory.NormalCoveringSymmetricKourovka18Problem23Wanted
