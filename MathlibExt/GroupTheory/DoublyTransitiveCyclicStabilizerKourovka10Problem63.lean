/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Torsion

/-!
# Doubly transitive groups with infinite cyclic point stabilizer (Kourovka Notebook Problem 10.63)

The proof uses the fixed-point argument in V. D. Mazurov, *2-Transitive permutation groups*,
Siberian Math. J. 31 (1990), 615–617, doi:10.1007/BF00970632. Rather than construct a field,
we use a recurrence in the subgroup of involutions to contradict infinite cyclicity.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.DoublyTransitiveCyclicStabilizerKourovka10Problem63Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 10.63 (Ya. P.
Sysak). UnsolvedMath record UM-00700678 (`KOU-10.63`), dataset ulamai/UnsolvedMath v1.8.0.

A permutation group is a faithful action (`FaithfulSMul`; without faithfulness `ℤ` acting trivially
on one point would qualify). Doubly transitive is `MulAction.IsMultiplyPretransitive G X 2`. The
action is transitive, so all point stabilizers are conjugate and one of them suffices.
-/

/-- **Doubly transitive group with infinite cyclic point stabilizer (Kourovka 10.63).** The
statement that there exist a group $G$ and a faithful action of $G$ on a set $X$ such that for
any two ordered pairs of distinct points of $X$ some element of $G$ maps the first to the second,
and the stabilizer of some point $x \in X$ is isomorphic to the infinite cyclic group $\mathbb{Z}$.
-/
def doublyTransitiveInfiniteCyclicStabilizer : Prop :=
  ∃ (G X : Type) (_ : Group G) (_ : MulAction G X), FaithfulSMul G X ∧
    MulAction.IsMultiplyPretransitive G X 2 ∧
    ∃ x : X, Nonempty (MulAction.stabilizer G x ≃* Multiplicative ℤ)

private theorem exists_pair_smul {G X : Type*} [Group G] [MulAction G X]
    (h₂ : MulAction.IsMultiplyPretransitive G X 2) {x y u v : X}
    (hxy : x ≠ y) (huv : u ≠ v) : ∃ g : G, g • x = u ∧ g • y = v := by
  let pair (a b : X) (hab : a ≠ b) : Fin 2 ↪ X :=
    ⟨![a, b], by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all⟩
  obtain ⟨g, hg⟩ := MulAction.isMultiplyPretransitive_iff.mp h₂ (pair x y hxy) (pair u v huv)
  exact ⟨g, congrArg (fun f : Fin 2 ↪ X ↦ f 0) hg, congrArg (fun f : Fin 2 ↪ X ↦ f 1) hg⟩

section

variable {G X : Type*} [Group G] [MulAction G X]

private theorem commute_of_stabilizer_equiv {x : X}
    (e : MulAction.stabilizer G x ≃* Multiplicative ℤ) {g h : G}
    (hg : g • x = x) (hh : h • x = x) : g * h = h * g := by
  let a : MulAction.stabilizer G x := ⟨g, hg⟩
  let b : MulAction.stabilizer G x := ⟨h, hh⟩
  have hab : a * b = b * a := e.injective (by simp [mul_comm])
  exact congrArg Subtype.val hab

private theorem eq_one_of_stabilizer_square_eq_one {x : X}
    (e : MulAction.stabilizer G x ≃* Multiplicative ℤ) {g : G} (hg : g • x = x)
    (hgg : g * g = 1) : g = 1 := by
  let a : MulAction.stabilizer G x := ⟨g, hg⟩
  have ha : a * a = 1 := Subtype.ext hgg
  have h : (e a).toAdd + (e a).toAdd = 0 := by
    simpa using congrArg (fun b ↦ (e b).toAdd) ha
  have ha' : e a = 1 := by
    change (e a).toAdd = 0
    omega
  exact congrArg Subtype.val (e.injective (ha'.trans e.map_one.symm))

private theorem eq_one_of_fix_pair [FaithfulSMul G X]
    (h₂ : MulAction.IsMultiplyPretransitive G X 2) {x y : X}
    (e : MulAction.stabilizer G x ≃* Multiplicative ℤ) (hxy : x ≠ y)
    {g : G} (hx : g • x = x) (hy : g • y = y) : g = 1 := by
  apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
  intro z
  rw [one_smul]
  by_cases hz : x = z
  · simpa [← hz] using hx
  obtain ⟨k, hkx, hky⟩ := exists_pair_smul h₂ hxy hz
  calc
    g • z = (g * k) • y := by rw [mul_smul, hky]
    _ = z := by rw [commute_of_stabilizer_equiv e hx hkx, mul_smul, hy, hky]

private theorem pair_unique [FaithfulSMul G X]
    (h₂ : MulAction.IsMultiplyPretransitive G X 2)
    (e : ∀ x : X, MulAction.stabilizer G x ≃* Multiplicative ℤ)
    {x y : X} (hxy : x ≠ y) {g h : G} (hx : g • x = h • x) (hy : g • y = h • y) :
    g = h := by
  have he : g⁻¹ * h = 1 := eq_one_of_fix_pair h₂ (e x) hxy
    (by rw [mul_smul, ← hx, inv_smul_smul]) (by rw [mul_smul, ← hy, inv_smul_smul])
  calc
    g = g * (g⁻¹ * h) := by rw [he, mul_one]
    _ = h := by simp

private theorem swap_pair [FaithfulSMul G X]
    (h₂ : MulAction.IsMultiplyPretransitive G X 2)
    (e : ∀ x : X, MulAction.stabilizer G x ≃* Multiplicative ℤ) {x y : X} (hxy : x ≠ y) :
    ∃ p : G, p • x = y ∧ p • y = x ∧ p * p = 1 := by
  obtain ⟨p, hp, hp'⟩ := exists_pair_smul h₂ hxy hxy.symm
  exact ⟨p, hp, hp', eq_one_of_fix_pair h₂ (e x) hxy
    (by rw [mul_smul, hp, hp']) (by rw [mul_smul, hp', hp])⟩

-- If `h` is a nonidentity stabilizer element, a swap times `h` has a fixed point.
private theorem swap_mul_hasFixedPoint [FaithfulSMul G X]
    (h₂ : MulAction.IsMultiplyPretransitive G X 2)
    (e : ∀ x : X, MulAction.stabilizer G x ≃* Multiplicative ℤ)
    {o b : X} (hob : o ≠ b) {p h : G} (hpo : p • o = b) (hpb : p • b = o)
    (hho : h • o = o) (hh : h ≠ 1) : ∃ x : X, (p * h) • x = x := by
  have hhb : b ≠ h⁻¹ • b := by
    intro he
    apply hh
    exact eq_one_of_fix_pair h₂ (e o) hob hho
      ((congrArg (h • ·) he).trans (smul_inv_smul h b))
  obtain ⟨s, hsb, _, hss⟩ := swap_pair h₂ e hhb
  have hso : o ≠ s • o := by
    intro he
    have hs := eq_one_of_stabilizer_square_eq_one (e o) he.symm hss
    exact hhb (by simpa [hs] using hsb)
  obtain ⟨k, hko, hks⟩ := exists_pair_smul h₂ hso hob
  have hsso : s • (s • o) = o := by rw [← mul_smul, hss, one_smul]
  have hpk : p * k = k * s := pair_unique h₂ e hso
    (by rw [mul_smul, mul_smul, hko, hpo, hks])
    (by simp only [mul_smul, hks, hpb, hsso, hko])
  refine ⟨k • (h⁻¹ • b), ?_⟩
  calc
    (p * h) • (k • (h⁻¹ • b)) = (p * k) • b := by
      rw [mul_smul, ← mul_smul h, commute_of_stabilizer_equiv (e o) hho hko, mul_smul,
        smul_inv_smul, mul_smul]
    _ = k • (h⁻¹ • b) := by rw [hpk, mul_smul, hsb]

-- The identity and the fixed-point-free swaps are precisely the elements squaring to one.
private theorem square_eq_one_of_no_fixed [FaithfulSMul G X]
    (h₂ : MulAction.IsMultiplyPretransitive G X 2)
    (e : ∀ x : X, MulAction.stabilizer G x ≃* Multiplicative ℤ) (o : X) {g : G}
    (hg : ∀ x : X, g • x ≠ x) : g * g = 1 := by
  obtain ⟨p, hpo, hpb, hpp⟩ := swap_pair h₂ e (hg o).symm
  let h := p⁻¹ * g
  have hho : h • o = o := by rw [show h = p⁻¹ * g from rfl, mul_smul, ← hpo, inv_smul_smul]
  have hph : p * h = g := by simp [h]
  by_cases hh : h = 1
  · rw [hh, mul_one] at hph
    exact hph ▸ hpp
  obtain ⟨x, hx⟩ := swap_mul_hasFixedPoint h₂ e (hg o).symm hpo hpb hho hh
  exact (hg x (hph ▸ hx)).elim

private def swapSubgroup [FaithfulSMul G X]
    (h₂ : MulAction.IsMultiplyPretransitive G X 2)
    (e : ∀ x : X, MulAction.stabilizer G x ≃* Multiplicative ℤ) (o : X) : Subgroup G where
  carrier := {g | g * g = 1}
  one_mem' := one_mul 1
  inv_mem' {g} hg := by
    change g * g = 1 at hg
    change g⁻¹ * g⁻¹ = 1
    simpa only [mul_inv_rev, inv_one] using congrArg Inv.inv hg
  mul_mem' {g h} hg hh := by
    change g * g = 1 at hg
    change h * h = 1 at hh
    change (g * h) * (g * h) = 1
    by_cases hg₁ : g = 1
    · simpa [hg₁] using hh
    by_cases hh₁ : h = 1
    · simpa [hh₁] using hg
    by_cases he : g = h
    · rw [he, hh, one_mul]
    apply square_eq_one_of_no_fixed h₂ e o
    intro x hx
    rw [mul_smul] at hx
    have hxy : x ≠ h • x := fun hf ↦ hh₁ (eq_one_of_stabilizer_square_eq_one (e x) hf.symm hh)
    have hgx : g • x = h • x := calc
      g • x = g • (g • (h • x)) := congrArg (g • ·) hx.symm
      _ = h • x := by rw [← mul_smul, hg, one_smul]
    have hhx : h • (h • x) = x := by rw [← mul_smul, hh, one_smul]
    exact he (pair_unique h₂ e hxy hgx (hx.trans hhx.symm))

end

-- A finite initial segment generates the whole forward sequence if there is a recurrence.
private theorem false_of_recurrence {J : Type*} [CommGroup J] (hsq : ∀ q : J, q * q = 1)
    {t : ℤ → J} (ht : Function.Injective t) {k l : ℤ} (hk : 0 < k) (hkl : k < l)
    (hrec : ∀ n : ℤ, t (n + l) = t n * t (n + k)) : False := by
  have hl : 0 < l := hk.trans hkl
  let S := Set.range (fun i : Fin l.toNat ↦ t i.val)
  let K := Subgroup.closure S
  have : Finite S := (Set.finite_range _).to_subtype
  have : Group.FG K := inferInstanceAs (Group.FG (Subgroup.closure S))
  have hsqK (q : K) : q * q = 1 := Subtype.ext (hsq q)
  have : Finite K := CommGroup.finite_of_fg_isMulTorsion K fun q ↦
    isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, by rw [pow_two, hsqK]⟩
  have hmem (n : ℕ) : t n ∈ K := by
    induction n using Nat.strongRecOn with
    | ind n ih =>
      by_cases hn : n < l.toNat
      · exact Subgroup.subset_closure ⟨⟨n, hn⟩, rfl⟩
      have hn' : l ≤ (n : ℤ) := by omega
      let m := n - l.toNat
      have hm : (m : ℤ) + l = n := by dsimp [m]; omega
      have hmk : ((m + k.toNat : ℕ) : ℤ) = (m : ℤ) + k := by omega
      rw [← hm, hrec, ← hmk]
      exact K.mul_mem (ih m (by omega)) (ih (m + k.toNat) (by omega))
  have : Finite ℕ := Finite.of_injective (fun n : ℕ ↦ (⟨t n, hmem n⟩ : K))
    (fun _ _ hij ↦ Int.ofNat_inj.mp (ht (congrArg Subtype.val hij)))
  exact not_finite ℕ

private theorem false_of_three_term_relation {J : Type*} [CommGroup J]
    (hsq : ∀ q : J, q * q = 1) {t : ℤ → J} (ht : Function.Injective t)
    {m : ℤ} (hm₀ : m ≠ 0) (hm₁ : m ≠ 1)
    (hm : ∀ n : ℤ, t n * t (n + 1) = t (n + m)) : False := by
  by_cases h : 1 < m
  · exact false_of_recurrence hsq ht (by decide : (0 : ℤ) < 1) h fun n ↦ (hm n).symm
  have hk : 0 < -m := by omega
  refine false_of_recurrence hsq ht hk (show -m < -m + 1 by omega) fun n ↦ ?_
  have hn := hm (n + -m)
  rw [show n + -m + m = n by omega] at hn
  calc
    t (n + (-m + 1)) = t (n + -m) * (t (n + -m) * t (n + -m + 1)) := by
      rw [← mul_assoc, hsq, one_mul, add_assoc]
    _ = t n * t (n + -m) := by rw [hn, mul_comm]

/--
**No doubly transitive group has an infinite cyclic point stabilizer (Kourovka 10.63).** If a group
$G$ acts faithfully on a set $X$ such that for any two ordered pairs of distinct points of $X$
some element of $G$ maps the first to the second, then no point stabilizer of the action is
isomorphic to the infinite cyclic group $\mathbb{Z}$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 10.63 (Ya. P.
Sysak); resolution: V. D. Mazurov, Siberian Math. J. 31 (1990), 615-617; Gy. Károlyi, S. J. Kovács
and P. P. Pálfy, Aequationes Math. 39, no. 1 (1990), 161-166, Kourovka Archive, Problem 10.63
("No").
-/
public theorem doublyTransitiveInfiniteCyclicStabilizer_refuted :
    ¬ doublyTransitiveInfiniteCyclicStabilizer := by
  rintro ⟨G, X, _, _, _, h₂, o, ⟨e₀⟩⟩
  let a : MulAction.stabilizer G o := e₀.symm (Multiplicative.ofAdd 1)
  have ha : a ≠ 1 := by
    intro h
    have h' := congrArg (fun b ↦ (e₀ b).toAdd) h
    simp [a] at h'
  obtain ⟨b, hob⟩ : ∃ b : X, o ≠ b := by
    by_contra! h
    apply ha
    apply Subtype.ext
    apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
    intro x
    change (a : G) • x = (1 : G) • x
    rw [← h x, one_smul]
    exact a.property
  have e : ∀ x : X, MulAction.stabilizer G x ≃* Multiplicative ℤ := by
    intro x
    by_cases hx : o = x
    · exact hx ▸ e₀
    have hex := exists_pair_smul (G := G) h₂ hob (Ne.symm hx)
    let g := hex.choose
    have hg : g • o = x := hex.choose_spec.1
    exact (MulAction.stabilizerEquivStabilizer hg.symm).symm.trans e₀
  rcases swap_pair h₂ e hob with ⟨p, hpo, _, hpp⟩
  let J := swapSubgroup h₂ e o
  have hSq (q : J) : q * q = 1 := Subtype.ext q.property
  have hInv (q : J) : q⁻¹ = q := calc
    q⁻¹ = q⁻¹ * (q * q) := by rw [hSq, mul_one]
    _ = q := by simp
  let : CommGroup J :=
    { (inferInstance : Group J) with
      mul_comm := fun q r ↦ by rw [← hInv (q * r), mul_inv_rev, hInv, hInv] }
  let t (n : ℤ) : J := ⟨MulAut.conj ((a : G) ^ n) p, by
    change MulAut.conj ((a : G) ^ n) p * MulAut.conj ((a : G) ^ n) p = 1
    rw [← map_mul, hpp, map_one]⟩
  -- The conjugates exhaust the nonidentity elements of `J`, and are all distinct.
  have htPoint (n : ℤ) : (t n : G) • o = (a : G) ^ n • b := by
    have hx : (a : G) ^ n • o = o := (a ^ n).property
    have hx' : ((a : G) ^ n)⁻¹ • o = o := (eq_inv_smul_iff.mpr hx).symm
    change ((a : G) ^ n * p * ((a : G) ^ n)⁻¹) • o = _
    rw [mul_smul, hx', mul_smul, hpo]
  have hconj (n : ℤ) : (a : G) ^ n ∈ MulAction.stabilizer G o := (a ^ n).property
  have haPow (n : ℤ) : (e₀ (a ^ n)).toAdd = n := by simp [a]
  have htInj : Function.Injective t := by
    intro n m he
    have hx : (a : G) ^ n • b = (a : G) ^ m • b := by rw [← htPoint, ← htPoint, he]
    have hnm : (a : G) ^ n = (a : G) ^ m :=
      pair_unique h₂ e hob ((hconj n).trans (hconj m).symm) hx
    have h' := congrArg (fun c ↦ (e₀ c).toAdd) (Subtype.ext hnm : a ^ n = a ^ m)
    simpa only [haPow] using h'
  have htSurj (q : J) (hq : q ≠ 1) : ∃ n : ℤ, t n = q := by
    have hqq : (q : G) * q = 1 := q.property
    have hqo : o ≠ (q : G) • o := fun hf ↦ hq (Subtype.ext
      (eq_one_of_stabilizer_square_eq_one (e o) hf.symm hqq))
    obtain ⟨g, hgo, hgb⟩ := exists_pair_smul h₂ hob hqo
    let k : MulAction.stabilizer G o := ⟨g, hgo⟩
    let n := (e₀ k).toAdd
    have hk : a ^ n = k := e₀.injective (by exact haPow n)
    have hx : (t n : G) • o = (q : G) • o := by
      rw [htPoint, ← Subgroup.coe_zpow, hk]; exact hgb
    have htSq : (t n : G) * (t n : G) = 1 := (t n).property
    refine ⟨n, Subtype.ext (pair_unique h₂ e hqo hx ?_)⟩
    rw [← hx, ← mul_smul, htSq, one_smul, hx, ← mul_smul, hqq, one_smul]
  have htNe (n : ℤ) : t n ≠ 1 := by
    intro he
    have hx : (a : G) ^ n • b = o := by rw [← htPoint, he]; exact one_smul G o
    have hy : (a : G) ^ n • o = (a : G) ^ n • b := (hconj n).trans hx.symm
    apply hob
    simpa only [inv_smul_smul] using congrArg (fun x : X ↦ ((a : G) ^ n)⁻¹ • x) hy
  have hprod : t 0 * t 1 ≠ 1 := by
    intro he
    have h01 : t 0 = t 1 := calc
      t 0 = t 0 * (t 0 * t 1) := by rw [he, mul_one]
      _ = t 1 := by rw [← mul_assoc, hSq, one_mul]
    exact zero_ne_one (htInj h01)
  obtain ⟨m, hm⟩ := htSurj _ hprod
  have hm₀ : m ≠ 0 := by
    intro he
    rw [he] at hm
    exact htNe 1 (mul_left_cancel (hm.symm.trans (mul_one _).symm))
  have hm₁ : m ≠ 1 := by
    intro he
    rw [he] at hm
    exact htNe 0 (mul_right_cancel (hm.symm.trans (one_mul _).symm))
  have htShift (n i : ℤ) : (t (n + i) : G) = MulAut.conj ((a : G) ^ n) (t i : G) := by
    simp [t, zpow_add]
  apply false_of_three_term_relation hSq htInj hm₀ hm₁
  intro n
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, map_mul, ← htShift, add_zero] using
    (congrArg (fun q : J ↦ MulAut.conj ((a : G) ^ n) (q : G)) hm).symm

end MathlibExt.GroupTheory.DoublyTransitiveCyclicStabilizerKourovka10Problem63Wanted
