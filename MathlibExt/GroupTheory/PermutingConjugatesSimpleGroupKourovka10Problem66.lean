/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Simple groups with permuting conjugate subgroups (Kourovka Notebook Problem 10.66)

Kourovka Notebook, Archive of Solved Problems, Problem 10.66 (A. N. Fomin, V. P. Shunkov): is a
group `G` non-simple if it contains two non-trivial subgroups `A` and `B` such that `AB ≠ G` and
`AB^g = B^gA` for every `g ∈ G`? This is true if `G` is finite (O. H. Kegel).

`permutingConjugatesNotSimple_refuted` shows that the answer is no in general. As in Bludov's
example, `A` and the conjugates of `B` form a chain under inclusion, so that `A B^g` and `B^g A`
are both the larger of the two subgroups. The proof takes for `G` the group of order automorphisms
of `ℚ` with bounded support, in place of a simple linearly ordered group, and for `A = B` the
subgroup of the elements that fix every point of `(-∞, 0]`: its conjugate by `g` is the subgroup of
the elements that fix every point of `(-∞, g 0]`.

The group `G` is simple. A nontrivial normal subgroup `N` contains an element `f` that moves an
open interval `I` off itself. For `g` and `h` supported in `I`, the element `f h⁻¹ f⁻¹` commutes
with `g`, so the commutator of `h` and `g` is the commutator of `h f h⁻¹ f⁻¹ ∈ N` and `g`, and lies
in `N`. Piecewise linear elements of `G` conjugate every bounded interval into `I`. Finally every
element is a commutator: an element `g` supported in `(1/2, 1)` equals `u v u⁻¹ v⁻¹`, where `v`
acts as `x ↦ x / 2` on `[0, 1]` and `u` is the product of the conjugates `vⁿ g v⁻ⁿ` (`n ≥ 0`), whose
supports are disjoint.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.PermutingConjugatesSimpleGroupKourovka10Problem66Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 10.66 (A. N.
Fomin, V. P. Shunkov). UnsolvedMath record UM-00700681 (`KOU-10.66`), dataset ulamai/UnsolvedMath
v1.8.0.

`B^g` ranges over all conjugates `g B g⁻¹`, and products of subgroups are set products.
-/

open scoped Pointwise

/-- **Permuting conjugates and simplicity (Kourovka 10.66).** The conjecture that a group $G$
containing nontrivial subgroups $A$ and $B$ such that the product set $AB$ is not all of $G$ and
$A \cdot gBg^{-1} = gBg^{-1} \cdot A$ for every $g \in G$ is not simple. Products of subgroups are
products of subsets of $G$.

This is Kourovka Problem 10.66 (A. N. Fomin, V. P. Shunkov). -/
def permutingConjugatesNotSimple : Prop :=
  ∀ (G : Type) [Group G] (A B : Subgroup G), A ≠ ⊥ → B ≠ ⊥ → (A : Set G) * (B : Set G) ≠ Set.univ →
    (∀ g : G, (A : Set G) * (B.map (MulAut.conj g).toMonoidHom : Set G) =
      (B.map (MulAut.conj g).toMonoidHom : Set G) * (A : Set G)) →
    ¬ IsSimpleGroup G

/-! ### Order automorphisms of `ℚ` with bounded support -/

private theorem perm_apply_inv (f : Equiv.Perm ℚ) (x : ℚ) : f (f⁻¹ x) = x :=
  Equiv.apply_symm_apply f x

private theorem perm_inv_apply (f : Equiv.Perm ℚ) (x : ℚ) : f⁻¹ (f x) = x :=
  Equiv.symm_apply_apply f x

/-- `σ` fixes every point outside the open interval `(a, b)`. -/
private def SuppIn (σ : Equiv.Perm ℚ) (a b : ℚ) : Prop :=
  ∀ x, x ≤ a ∨ b ≤ x → σ x = x

private theorem suppIn_mono {σ : Equiv.Perm ℚ} {a b a' b' : ℚ} (h : SuppIn σ a b) (ha : a' ≤ a)
    (hb : b ≤ b') : SuppIn σ a' b' := fun x hx =>
  h x (hx.imp (fun h' => h'.trans ha) (fun h' => hb.trans h'))

private theorem suppIn_inv {σ : Equiv.Perm ℚ} {a b : ℚ} (h : SuppIn σ a b) : SuppIn σ⁻¹ a b :=
  fun x hx => Equiv.Perm.inv_eq_iff_eq.mpr (h x hx).symm

private theorem strictMono_inv {σ : Equiv.Perm ℚ} (hσ : StrictMono σ) :
    StrictMono (σ⁻¹ : Equiv.Perm ℚ) := by
  intro x y hxy
  rw [← hσ.lt_iff_lt]
  simpa using hxy

/-- Order automorphisms of `ℚ` with bounded support. -/
private def boundedAut : Subgroup (Equiv.Perm ℚ) where
  carrier := {σ | StrictMono σ ∧ ∃ a b, SuppIn σ a b}
  one_mem' := ⟨strictMono_id, 0, 0, fun _ _ => rfl⟩
  mul_mem' := by
    rintro σ τ ⟨hσ, a, b, hσs⟩ ⟨hτ, c, d, hτs⟩
    refine ⟨by rw [Equiv.Perm.coe_mul]; exact hσ.comp hτ, min a c, max b d, fun x hx => ?_⟩
    have h1 : τ x = x := hτs x
      (hx.imp (fun h => h.trans (min_le_right _ _)) (fun h => (le_max_right _ _).trans h))
    have h2 : σ x = x := hσs x
      (hx.imp (fun h => h.trans (min_le_left _ _)) (fun h => (le_max_left _ _).trans h))
    rw [Equiv.Perm.mul_apply, h1, h2]
  inv_mem' := by
    rintro σ ⟨hσ, a, b, hσs⟩
    exact ⟨strictMono_inv hσ, a, b, suppIn_inv hσs⟩

private theorem suppIn_conj {c g : Equiv.Perm ℚ} (hc : StrictMono c) {a b p q : ℚ}
    (hg : SuppIn g a b) (hpa : p < c a) (hbq : c b < q) : SuppIn (c * g * c⁻¹) p q := by
  intro x hx
  have hy : c⁻¹ x ≤ a ∨ b ≤ c⁻¹ x := by
    rcases hx with hx | hx
    · left
      rw [← hc.le_iff_le, perm_apply_inv]
      linarith
    · right
      rw [← hc.le_iff_le, perm_apply_inv]
      linarith
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hg _ hy, perm_apply_inv]

/-! ### Piecewise linear maps -/

/-- The piecewise linear map that fixes `x ≤ L` and `x ≥ R` and sends `s` to `t`. -/
private def pl (L R s t x : ℚ) : ℚ :=
  if x ≤ s then (if x ≤ L then x else L + (x - L) * ((t - L) / (s - L)))
  else if R ≤ x then x else t + (x - s) * ((R - t) / (R - s))

private theorem pl_inv {L R s t : ℚ} (hLs : L < s) (hsR : s < R) (hLt : L < t) (htR : t < R)
    (x : ℚ) : pl L R t s (pl L R s t x) = x := by
  have k₁pos : 0 < (t - L) / (s - L) := div_pos (by linarith) (by linarith)
  have k₂pos : 0 < (R - t) / (R - s) := div_pos (by linarith) (by linarith)
  have hsL : s - L ≠ 0 := (sub_pos.mpr hLs).ne'
  have htL : t - L ≠ 0 := (sub_pos.mpr hLt).ne'
  have hRs : R - s ≠ 0 := (sub_pos.mpr hsR).ne'
  have hRt : R - t ≠ 0 := (sub_pos.mpr htR).ne'
  have e₁ : (s - L) * ((t - L) / (s - L)) = t - L := by field_simp
  have e₂ : (R - s) * ((R - t) / (R - s)) = R - t := by field_simp
  unfold pl
  by_cases hxs : x ≤ s
  · rw [ite_eq_left hxs]
    by_cases hxL : x ≤ L
    · rw [ite_eq_left hxL, ite_eq_left (by linarith), ite_eq_left hxL]
    · rw [ite_eq_right hxL]
      have hy1 : L + (x - L) * ((t - L) / (s - L)) ≤ t := by nlinarith
      have hy2 : ¬ L + (x - L) * ((t - L) / (s - L)) ≤ L := by
        push Not
        nlinarith
      rw [ite_eq_left hy1, ite_eq_right hy2]
      field_simp
      ring
  · rw [ite_eq_right hxs]
    by_cases hxR : R ≤ x
    · rw [ite_eq_left hxR, ite_eq_right (by linarith), ite_eq_left hxR]
    · rw [ite_eq_right hxR]
      have hy1 : ¬ t + (x - s) * ((R - t) / (R - s)) ≤ t := by
        push Not
        nlinarith
      have hy2 : ¬ R ≤ t + (x - s) * ((R - t) / (R - s)) := by
        push Not
        nlinarith
      rw [ite_eq_right hy1, ite_eq_right hy2]
      field_simp
      ring

private theorem pl_strictMono {L R s t : ℚ} (hLs : L < s) (hsR : s < R) (hLt : L < t)
    (htR : t < R) :
    StrictMono (pl L R s t) := by
  intro x y hxy
  have k₁pos : 0 < (t - L) / (s - L) := div_pos (by linarith) (by linarith)
  have k₂pos : 0 < (R - t) / (R - s) := div_pos (by linarith) (by linarith)
  have hsL : s - L ≠ 0 := (sub_pos.mpr hLs).ne'
  have hRs : R - s ≠ 0 := (sub_pos.mpr hsR).ne'
  have e₁ : (s - L) * ((t - L) / (s - L)) = t - L := by field_simp
  have e₂ : (R - s) * ((R - t) / (R - s)) = R - t := by field_simp
  unfold pl
  generalize (t - L) / (s - L) = k₁ at k₁pos e₁ ⊢
  generalize (R - t) / (R - s) = k₂ at k₂pos e₂ ⊢
  split_ifs <;> nlinarith

private theorem pl_suppIn {L R s t : ℚ} (hLs : L < s) (hsR : s < R) :
    ∀ x, x ≤ L ∨ R ≤ x → pl L R s t x = x := by
  intro x hx
  unfold pl
  rcases hx with hx | hx
  · rw [ite_eq_left (by linarith), ite_eq_left hx]
  · rw [ite_eq_right (by linarith), ite_eq_left hx]

private theorem pl_apply_self {L R s t : ℚ} (hLs : L < s) : pl L R s t s = t := by
  have hsL : s - L ≠ 0 := (sub_pos.mpr hLs).ne'
  unfold pl
  rw [ite_eq_left le_rfl, ite_eq_right (by linarith)]
  field_simp
  ring

/-- `pl L R s t` as a permutation of `ℚ`. -/
private def plPerm (L R s t : ℚ) (hLs : L < s) (hsR : s < R) (hLt : L < t) (htR : t < R) :
    Equiv.Perm ℚ where
  toFun := pl L R s t
  invFun := pl L R t s
  left_inv := pl_inv hLs hsR hLt htR
  right_inv := pl_inv hLt htR hLs hsR

private theorem plPerm_apply {L R s t : ℚ} (hLs : L < s) (hsR : s < R) (hLt : L < t) (htR : t < R)
    (x : ℚ) : plPerm L R s t hLs hsR hLt htR x = pl L R s t x := rfl

private theorem plPerm_mem {L R s t : ℚ} (hLs : L < s) (hsR : s < R) (hLt : L < t) (htR : t < R) :
    plPerm L R s t hLs hsR hLt htR ∈ boundedAut :=
  ⟨pl_strictMono hLs hsR hLt htR, L, R, pl_suppIn hLs hsR⟩

/-- Every bounded interval can be conjugated into any open interval. -/
private theorem exists_conj_into {a b p q : ℚ} (hab : a < b) (hpq : p < q) :
    ∃ c ∈ boundedAut, p < c a ∧ c b < q := by
  obtain ⟨m, hm⟩ : ∃ m, m = (p + q) / 2 := ⟨_, rfl⟩
  have hpm : p < m := by rw [hm]; linarith
  have hmq : m < q := by rw [hm]; linarith
  have h1 : min a m - 1 < a := by linarith [min_le_left a m]
  have h2 : a < max a m + 1 := by linarith [le_max_left a m]
  have h3 : min a m - 1 < m := by linarith [min_le_right a m]
  have h4 : m < max a m + 1 := by linarith [le_max_right a m]
  set c₁ := plPerm (min a m - 1) (max a m + 1) a m h1 h2 h3 h4 with hc₁
  have hc₁a : c₁ a = m := pl_apply_self h1
  have hc₁m : StrictMono c₁ := pl_strictMono h1 h2 h3 h4
  have hmb : m < c₁ b := by rw [← hc₁a]; exact hc₁m hab
  have h5 : c₁ b < max (c₁ b) q + 1 := by linarith [le_max_left (c₁ b) q]
  have h6 : m < (m + q) / 2 := by linarith
  have h7 : (m + q) / 2 < max (c₁ b) q + 1 := by linarith [le_max_right (c₁ b) q]
  set c₂ := plPerm m (max (c₁ b) q + 1) (c₁ b) ((m + q) / 2) hmb h5 h6 h7 with hc₂
  refine ⟨c₂ * c₁, boundedAut.mul_mem (plPerm_mem _ _ _ _) (plPerm_mem _ _ _ _), ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, hc₁a, hc₂, plPerm_apply, pl_suppIn hmb h5 m (Or.inl le_rfl)]
    exact hpm
  · rw [Equiv.Perm.mul_apply, hc₂, plPerm_apply, pl_apply_self hmb]
    linarith

/-! ### The commutator trick -/

/-- If `f` moves `(p, q)` off itself, normality gives all commutators supported in `(p, q)`. -/
private theorem commutator_mem {N : Subgroup (Equiv.Perm ℚ)}
    (hconj : ∀ c ∈ boundedAut, ∀ f ∈ N, c * f * c⁻¹ ∈ N) {f : Equiv.Perm ℚ} (hfN : f ∈ N)
    (hf : StrictMono f) {p q : ℚ} (hq : q ≤ f p) {g h : Equiv.Perm ℚ} (hg : g ∈ boundedAut)
    (hh : h ∈ boundedAut) (hgs : SuppIn g p q) (hhs : SuppIn h p q) :
    h * g * h⁻¹ * g⁻¹ ∈ N := by
  obtain ⟨k, hk⟩ : ∃ k, k = f * h⁻¹ * f⁻¹ := ⟨_, rfl⟩
  have hdisj : Equiv.Perm.Disjoint g k := by
    intro y
    by_cases hy : q ≤ y
    · exact Or.inl (hgs y (Or.inr hy))
    · right
      push Not at hy
      have h1 : f⁻¹ y ≤ p := by
        rw [← hf.le_iff_le, perm_apply_inv]
        linarith
      rw [hk, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, suppIn_inv hhs _ (Or.inl h1),
        perm_apply_inv]
  have hc : k * g = g * k := hdisj.commute.eq.symm
  have hX : h * f * h⁻¹ * f⁻¹ ∈ N := N.mul_mem (hconj h hh f hfN) (N.inv_mem hfN)
  have hY := N.mul_mem hX (hconj g hg _ (N.inv_mem hX))
  have e : h * f * h⁻¹ * f⁻¹ * (g * (h * f * h⁻¹ * f⁻¹)⁻¹ * g⁻¹) = h * g * h⁻¹ * g⁻¹ := by
    have hXk : h * f * h⁻¹ * f⁻¹ = h * k := by rw [hk]; group
    rw [hXk]
    calc h * k * (g * (h * k)⁻¹ * g⁻¹) = h * (k * g) * k⁻¹ * h⁻¹ * g⁻¹ := by group
      _ = h * (g * k) * k⁻¹ * h⁻¹ * g⁻¹ := by rw [hc]
      _ = h * g * h⁻¹ * g⁻¹ := by group
  rwa [e] at hY

/-! ### Infinite products -/

private theorem exists_lvl {x : ℚ} (hx : 0 < x) : ∃ n : ℕ, 1 < 2 ^ (n + 1) * x := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / x) (by norm_num : (1 : ℚ) < 2)
  refine ⟨n, ?_⟩
  rw [div_lt_iff₀ hx] at hn
  have : (0 : ℚ) < 2 ^ n * x := by positivity
  rw [pow_succ]
  nlinarith

/-- The level of `x ∈ (0, 1]`: the `n` with `2⁻ⁿ⁻¹ < x ≤ 2⁻ⁿ`. -/
private def lvl (x : ℚ) : ℕ := if h : 0 < x then Nat.find (exists_lvl h) else 0

private theorem lvl_spec {x : ℚ} (hx : 0 < x) (hx1 : x ≤ 1) :
    1 < 2 ^ (lvl x + 1) * x ∧ 2 ^ lvl x * x ≤ 1 := by
  rw [lvl, dite_eq_left hx]
  refine ⟨Nat.find_spec (exists_lvl hx), ?_⟩
  rcases h : Nat.find (exists_lvl hx) with _ | n
  · simpa using hx1
  · have := Nat.find_min (exists_lvl hx) (show n < Nat.find (exists_lvl hx) by omega)
    push Not at this
    exact this

private theorem pos_of_lvl {x : ℚ} {n : ℕ} (h1 : 1 < 2 ^ (n + 1) * x) (h2 : 2 ^ n * x ≤ 1) :
    0 < x ∧ x ≤ 1 := by
  have hx : 0 < x := by
    by_contra h
    push Not at h
    have : (2 : ℚ) ^ (n + 1) * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    linarith
  refine ⟨hx, ?_⟩
  have : (1 : ℚ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  nlinarith

private theorem lvl_eq {x : ℚ} {n : ℕ} (h1 : 1 < 2 ^ (n + 1) * x) (h2 : 2 ^ n * x ≤ 1) :
    lvl x = n := by
  obtain ⟨hx, hx1⟩ := pos_of_lvl h1 h2
  obtain ⟨hl1, hl2⟩ := lvl_spec hx hx1
  rcases lt_trichotomy (lvl x) n with h | h | h
  · have : (2 : ℚ) ^ (lvl x + 1) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) h
    nlinarith
  · exact h
  · have : (2 : ℚ) ^ (n + 1) ≤ 2 ^ lvl x := pow_le_pow_right₀ (by norm_num) h
    nlinarith

/-- The infinite product of the conjugates of `g` by the powers of `x ↦ x / 2`. -/
private def stack (g : Equiv.Perm ℚ) (x : ℚ) : ℚ :=
  if 0 < x ∧ x ≤ 1 then g (2 ^ lvl x * x) / 2 ^ lvl x else x

private theorem stack_eq (g : Equiv.Perm ℚ) {x : ℚ} {n : ℕ} (h1 : 1 < 2 ^ (n + 1) * x)
    (h2 : 2 ^ n * x ≤ 1) : stack g x = g (2 ^ n * x) / 2 ^ n := by
  rw [stack, ite_eq_left (pos_of_lvl h1 h2), lvl_eq h1 h2]

private theorem stack_of_not (g : Equiv.Perm ℚ) {x : ℚ} (h : ¬ (0 < x ∧ x ≤ 1)) :
    stack g x = x := by
  rw [stack, ite_eq_right h]

private theorem good_maps {g : Equiv.Perm ℚ} (hg : StrictMono g) (hgs : SuppIn g (1 / 2) 1) {y : ℚ}
    (hy1 : 1 / 2 < y) (hy2 : y ≤ 1) : 1 / 2 < g y ∧ g y ≤ 1 := by
  have a := hgs (1 / 2) (Or.inl le_rfl)
  have b := hgs 1 (Or.inr le_rfl)
  constructor
  · calc (1 / 2 : ℚ) = g (1 / 2) := a.symm
      _ < g y := hg hy1
  · calc g y ≤ g 1 := hg.monotone hy2
      _ = 1 := b

private theorem stack_level {g : Equiv.Perm ℚ} (hg : StrictMono g) (hgs : SuppIn g (1 / 2) 1)
    {x : ℚ} {n : ℕ} (h1 : 1 < 2 ^ (n + 1) * x) (h2 : 2 ^ n * x ≤ 1) :
    1 < 2 ^ (n + 1) * stack g x ∧ 2 ^ n * stack g x ≤ 1 := by
  rw [stack_eq g h1 h2]
  have hy1 : 1 / 2 < 2 ^ n * x := by rw [pow_succ] at h1; linarith
  obtain ⟨a, b⟩ := good_maps hg hgs hy1 h2
  have hpos : (0 : ℚ) < 2 ^ n := by positivity
  have e1 : (2 : ℚ) ^ (n + 1) * (g (2 ^ n * x) / 2 ^ n) = 2 * g (2 ^ n * x) := by
    rw [pow_succ]; field_simp
  have e2 : (2 : ℚ) ^ n * (g (2 ^ n * x) / 2 ^ n) = g (2 ^ n * x) := by
    field_simp
  rw [e1, e2]
  constructor <;> linarith

private theorem stack_mem {g : Equiv.Perm ℚ} (hg : StrictMono g) (hgs : SuppIn g (1 / 2) 1)
    {x : ℚ} (hx : 0 < x ∧ x ≤ 1) : 0 < stack g x ∧ stack g x ≤ 1 := by
  obtain ⟨h1, h2⟩ := lvl_spec hx.1 hx.2
  obtain ⟨k1, k2⟩ := stack_level hg hgs h1 h2
  exact pos_of_lvl k1 k2

private theorem stack_inv {g : Equiv.Perm ℚ} (hg : StrictMono g) (hgs : SuppIn g (1 / 2) 1)
    (x : ℚ) :
    stack g⁻¹ (stack g x) = x := by
  by_cases hx : 0 < x ∧ x ≤ 1
  · obtain ⟨h1, h2⟩ := lvl_spec hx.1 hx.2
    obtain ⟨h1', h2'⟩ := stack_level hg hgs h1 h2
    rw [stack_eq g⁻¹ h1' h2', stack_eq g h1 h2]
    have hpos : (0 : ℚ) < 2 ^ lvl x := by positivity
    have e : (2 : ℚ) ^ lvl x * (g (2 ^ lvl x * x) / 2 ^ lvl x) = g (2 ^ lvl x * x) := by
      field_simp
    rw [e, perm_inv_apply]
    field_simp
  · rw [stack_of_not g hx, stack_of_not g⁻¹ hx]

private theorem stack_strictMono {g : Equiv.Perm ℚ} (hg : StrictMono g) (hgs : SuppIn g (1 / 2) 1) :
    StrictMono (stack g) := by
  intro x y hxy
  by_cases hx : 0 < x ∧ x ≤ 1 <;> by_cases hy : 0 < y ∧ y ≤ 1
  · obtain ⟨h1, h2⟩ := lvl_spec hx.1 hx.2
    obtain ⟨k1, k2⟩ := lvl_spec hy.1 hy.2
    have hmn : lvl y ≤ lvl x := by
      by_contra hc
      push Not at hc
      have : (2 : ℚ) ^ (lvl x + 1) ≤ 2 ^ lvl y := pow_le_pow_right₀ (by norm_num) hc
      nlinarith [mul_le_mul_of_nonneg_right this hy.1.le,
        mul_lt_mul_of_pos_left hxy (by positivity : (0 : ℚ) < 2 ^ (lvl x + 1))]
    rcases hmn.lt_or_eq with hlt | heq
    · obtain ⟨a1, a2⟩ := stack_level hg hgs h1 h2
      obtain ⟨b1, b2⟩ := stack_level hg hgs k1 k2
      have hsx := (stack_mem hg hgs hx).1
      have : (2 : ℚ) ^ (lvl y + 1) ≤ 2 ^ lvl x := pow_le_pow_right₀ (by norm_num) hlt
      have hp : (0 : ℚ) < 2 ^ (lvl y + 1) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right this hsx.le]
    · rw [stack_eq g h1 h2, stack_eq g k1 k2, heq]
      have hpos : (0 : ℚ) < 2 ^ lvl x := by positivity
      exact div_lt_div_of_pos_right (hg (mul_lt_mul_of_pos_left hxy hpos)) hpos
  · have hy1 : 1 < y := by
      by_contra hc
      push Not at hc
      exact hy ⟨hx.1.trans hxy, hc⟩
    rw [stack_of_not g hy]
    linarith [(stack_mem hg hgs hx).2]
  · have hx0 : x ≤ 0 := by
      by_contra hc
      push Not at hc
      exact hx ⟨hc, hxy.le.trans hy.2⟩
    rw [stack_of_not g hx]
    linarith [(stack_mem hg hgs hy).1]
  · rw [stack_of_not g hx, stack_of_not g hy]
    exact hxy

private theorem stack_suppIn {g : Equiv.Perm ℚ} (hgs : SuppIn g (1 / 2) 1) :
    ∀ x, x ≤ 0 ∨ 1 ≤ x → stack g x = x := by
  intro x hx
  rcases hx with hx | hx
  · exact stack_of_not g (fun h => by linarith [h.1])
  · rcases hx.lt_or_eq with hx | rfl
    · exact stack_of_not g (fun h => by linarith [h.2])
    · rw [stack_eq g (n := 0) (by norm_num) (by norm_num)]
      simp [hgs 1 (Or.inr le_rfl)]

/-- `pl 0 2 1 (1 / 2)` halves `[0, 1]`. -/
private theorem shift_of_le {x : ℚ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : pl 0 2 1 (1 / 2) x = x / 2 := by
  unfold pl
  rw [ite_eq_left h1]
  split_ifs with h
  · linarith
  · ring

/-- The infinite product `u = stack g` and the shift `v = pl 0 2 1 (1 / 2)` satisfy
`u ∘ v = g ∘ v ∘ u`. -/
private theorem stack_comm {g : Equiv.Perm ℚ} (hg : StrictMono g) (hgs : SuppIn g (1 / 2) 1)
    (x : ℚ) : stack g (pl 0 2 1 (1 / 2) x) = g (pl 0 2 1 (1 / 2) (stack g x)) := by
  rcases le_or_gt x 0 with hx | hx
  · have hv : pl 0 2 1 (1 / 2) x = x := pl_suppIn (by norm_num) (by norm_num) x (Or.inl hx)
    rw [hv, stack_of_not g (fun h => by linarith [h.1]), hv, hgs x (Or.inl (by linarith))]
  rcases le_or_gt x 1 with hx1 | hx1
  · obtain ⟨h1, h2⟩ := lvl_spec hx hx1
    have hsx := stack_mem hg hgs ⟨hx, hx1⟩
    rw [shift_of_le hx.le hx1, shift_of_le hsx.1.le hsx.2,
      hgs _ (Or.inl (by linarith [hsx.2]))]
    have k1 : 1 < 2 ^ (lvl x + 1 + 1) * (x / 2) := by
      rw [pow_succ]; field_simp; linarith
    have k2 : 2 ^ (lvl x + 1) * (x / 2) ≤ 1 := by
      rw [pow_succ]; field_simp; linarith
    rw [stack_eq g k1 k2, stack_eq g h1 h2]
    have e : (2 : ℚ) ^ (lvl x + 1) * (x / 2) = 2 ^ lvl x * x := by
      rw [pow_succ]; ring
    rw [e, pow_succ]
    field_simp
  have hsx : stack g x = x := stack_of_not g (fun h => by linarith [h.2])
  rw [hsx]
  rcases le_or_gt 2 x with hx2 | hx2
  · have hv : pl 0 2 1 (1 / 2) x = x := pl_suppIn (by norm_num) (by norm_num) x (Or.inr hx2)
    rw [hv, stack_of_not g (fun h => by linarith [h.2]), hgs x (Or.inr (by linarith))]
  · have hv : pl 0 2 1 (1 / 2) x = 1 / 2 + (x - 1) * ((2 - 1 / 2) / (2 - 1)) := by
      unfold pl
      rw [ite_eq_right (by linarith), ite_eq_right (by linarith)]
    rw [hv]
    set w := 1 / 2 + (x - 1) * ((2 - 1 / 2) / (2 - 1) : ℚ) with hw
    have hw1 : 1 / 2 < w := by rw [hw]; norm_num; linarith
    rcases le_or_gt w 1 with hw2 | hw2
    · rw [stack_eq g (n := 0) (by norm_num; linarith) (by norm_num; linarith)]
      simp
    · rw [stack_of_not g (fun h => by linarith [h.2]), hgs w (Or.inr hw2.le)]

/-- The infinite product as a permutation. -/
private def stackPerm (g : Equiv.Perm ℚ) (hg : StrictMono g) (hgs : SuppIn g (1 / 2) 1) :
    Equiv.Perm ℚ where
  toFun := stack g
  invFun := stack g⁻¹
  left_inv := stack_inv hg hgs
  right_inv := by
    intro x
    have h := stack_inv (g := g⁻¹) (strictMono_inv hg) (suppIn_inv hgs) x
    rwa [inv_inv] at h

/-- The shift `x ↦ x / 2` on `[0, 1]`, as an element of the group. -/
private def vPerm : Equiv.Perm ℚ :=
  plPerm 0 2 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem vPerm_mem : vPerm ∈ boundedAut := plPerm_mem _ _ _ _

/-- Every element supported in `(1 / 2, 1)` is a commutator. -/
private theorem exists_commutator {g : Equiv.Perm ℚ} (hg : g ∈ boundedAut)
    (hgs : SuppIn g (1 / 2) 1) :
    ∃ u ∈ boundedAut, ∃ v ∈ boundedAut, SuppIn u 0 2 ∧ SuppIn v 0 2 ∧ g = u * v * u⁻¹ * v⁻¹ := by
  refine ⟨stackPerm g hg.1 hgs, ⟨stack_strictMono hg.1 hgs, 0, 1, stack_suppIn hgs⟩, vPerm,
    vPerm_mem, suppIn_mono (σ := stackPerm g hg.1 hgs) (stack_suppIn hgs) le_rfl (by norm_num),
    pl_suppIn (by norm_num) (by norm_num), ?_⟩
  have h : stackPerm g hg.1 hgs * vPerm = g * vPerm * stackPerm g hg.1 hgs := by
    ext x
    exact stack_comm hg.1 hgs x
  calc g = g * vPerm * stackPerm g hg.1 hgs * (stackPerm g hg.1 hgs)⁻¹ * vPerm⁻¹ := by group
    _ = _ := by rw [h]

/-! ### Simplicity -/

/-- A subgroup of `boundedAut` that is normalized by `boundedAut` and contains a nontrivial element
is all of `boundedAut`. -/
private theorem le_of_mem_ne_one {N : Subgroup (Equiv.Perm ℚ)} (hN : N ≤ boundedAut)
    (hconj : ∀ c ∈ boundedAut, ∀ f ∈ N, c * f * c⁻¹ ∈ N) {f : Equiv.Perm ℚ} (hfN : f ∈ N)
    (hf1 : f ≠ 1) : boundedAut ≤ N := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ x := by
    by_contra h
    push Not at h
    exact hf1 (Equiv.ext h)
  have hfm := (hN hfN).1
  obtain ⟨F, hFN, hFm, hxF⟩ : ∃ F ∈ N, StrictMono F ∧ x < F x := by
    rcases lt_or_gt_of_ne hx with h | h
    · refine ⟨f⁻¹, N.inv_mem hfN, strictMono_inv hfm, ?_⟩
      rw [← hfm.lt_iff_lt, perm_apply_inv]
      exact h
    · exact ⟨f, hfN, hfm, h⟩
  intro k hk
  obtain ⟨hkm, a, b, hks⟩ := hk
  have hks' : SuppIn k a (max b (a + 1)) := suppIn_mono hks le_rfl (le_max_left _ _)
  have hab : a < max b (a + 1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  obtain ⟨c₁, hc₁, hc₁a, hc₁b⟩ := exists_conj_into hab (show (1 / 2 : ℚ) < 1 by norm_num)
  have hk' : c₁ * k * c₁⁻¹ ∈ boundedAut :=
    boundedAut.mul_mem (boundedAut.mul_mem hc₁ ⟨hkm, a, b, hks⟩) (boundedAut.inv_mem hc₁)
  obtain ⟨u, hu, v, hv, hus, hvs, hkuv⟩ :=
    exists_commutator hk' (suppIn_conj hc₁.1 hks' hc₁a hc₁b)
  obtain ⟨c₂, hc₂, hc₂0, hc₂2⟩ := exists_conj_into (show (0 : ℚ) < 2 by norm_num) hxF
  have hmem := commutator_mem hconj hFN hFm (le_refl (F x))
    (boundedAut.mul_mem (boundedAut.mul_mem hc₂ hv) (boundedAut.inv_mem hc₂))
    (boundedAut.mul_mem (boundedAut.mul_mem hc₂ hu) (boundedAut.inv_mem hc₂))
    (suppIn_conj hc₂.1 hvs hc₂0 hc₂2) (suppIn_conj hc₂.1 hus hc₂0 hc₂2)
  have e : k = (c₂ * c₁)⁻¹ * ((c₂ * u * c₂⁻¹) * (c₂ * v * c₂⁻¹) * (c₂ * u * c₂⁻¹)⁻¹ *
      (c₂ * v * c₂⁻¹)⁻¹) * ((c₂ * c₁)⁻¹)⁻¹ := by
    have : (c₂ * u * c₂⁻¹) * (c₂ * v * c₂⁻¹) * (c₂ * u * c₂⁻¹)⁻¹ * (c₂ * v * c₂⁻¹)⁻¹ =
        c₂ * (u * v * u⁻¹ * v⁻¹) * c₂⁻¹ := by group
    rw [this, ← hkuv]
    group
  rw [e]
  exact hconj _ (boundedAut.inv_mem (boundedAut.mul_mem hc₂ hc₁)) _ hmem

private theorem vPerm_ne_one : vPerm ≠ 1 := by
  intro h
  have := congrArg (fun σ : Equiv.Perm ℚ => σ 1) h
  simp only [vPerm, plPerm_apply, Equiv.Perm.coe_one, id_eq] at this
  rw [pl_apply_self (by norm_num)] at this
  norm_num at this

/-- The group of order automorphisms of `ℚ` with bounded support is simple. -/
private theorem boundedAut_isSimpleGroup : IsSimpleGroup boundedAut := by
  have : Nontrivial boundedAut := ⟨⟨⟨vPerm, vPerm_mem⟩, 1, fun h => vPerm_ne_one
    (congrArg Subtype.val h)⟩⟩
  refine ⟨fun H hH => ?_⟩
  rcases H.bot_or_exists_ne_one with hbot | ⟨f, hfH, hf1⟩
  · exact Or.inl hbot
  right
  have hle := le_of_mem_ne_one (N := H.map boundedAut.subtype)
    (fun _ ⟨y, _, hy⟩ => hy ▸ y.2)
    (fun c hc _ ⟨y, hy, hyx⟩ => ⟨⟨c, hc⟩ * y * ⟨c, hc⟩⁻¹, hH.conj_mem y hy _, by
      rw [← hyx]; rfl⟩)
    ⟨f, hfH, rfl⟩ (fun h => hf1 (Subtype.ext h))
  rw [eq_top_iff]
  intro k _
  obtain ⟨k₀, hk₀, hk⟩ := hle k.2
  rwa [show k = k₀ from Subtype.ext hk.symm]

/-! ### The subgroups -/

/-- The elements fixing `(-∞, 0]` pointwise. -/
private def fixNeg : Subgroup boundedAut where
  carrier := {f | ∀ x ≤ 0, (f : Equiv.Perm ℚ) x = x}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb x hx
    simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply]
    rw [hb x hx, ha x hx]
  inv_mem' := by
    intro a ha x hx
    simp only [Subgroup.coe_inv]
    exact Equiv.Perm.inv_eq_iff_eq.mpr (ha x hx).symm

private theorem coe_mul_of_le {G : Type*} [Group G] {H K : Subgroup G} (hHK : H ≤ K) :
    (H : Set G) * (K : Set G) = K ∧ (K : Set G) * (H : Set G) = K := by
  constructor
  · apply le_antisymm
    · exact Set.mul_subset_iff.mpr fun x hx y hy => K.mul_mem (hHK hx) hy
    · exact Set.subset_mul_right _ H.one_mem
  · apply le_antisymm
    · exact Set.mul_subset_iff.mpr fun x hx y hy => K.mul_mem hx (hHK hy)
    · exact Set.subset_mul_left _ H.one_mem

/-- Each conjugate of `fixNeg` contains `fixNeg` or is contained in it. -/
private theorem fixNeg_comparable (g : boundedAut) :
    fixNeg ≤ fixNeg.map (MulAut.conj g).toMonoidHom ∨
      fixNeg.map (MulAut.conj g).toMonoidHom ≤ fixNeg := by
  have hg : StrictMono (g : Equiv.Perm ℚ) := g.2.1
  rcases le_total ((g : Equiv.Perm ℚ) 0) 0 with h0 | h0
  · left
    intro f hf
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * f * g, ?_, ?_⟩
    · intro x hx
      have hgx : (g : Equiv.Perm ℚ) x ≤ 0 := (hg.monotone hx).trans h0
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
      rw [hf _ hgx, perm_inv_apply]
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  · right
    intro y hy
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hy
    intro x hx
    have hx' : (g : Equiv.Perm ℚ)⁻¹ x ≤ 0 := by
      rw [← hg.le_iff_le, perm_apply_inv]
      exact hx.trans h0
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      Equiv.Perm.mul_apply]
    rw [hf _ hx', perm_apply_inv]

/--
**A simple group with permuting conjugate subgroups (Kourovka 10.66 refuted).** There exist a
simple group $G$ and nontrivial subgroups $A$ and $B$ of $G$ such that the product set $AB$ is not
all of $G$ and $A \cdot gBg^{-1} = gBg^{-1} \cdot A$ for every $g \in G$, where products of
subgroups are products of subsets of $G$. So the conjecture of Kourovka Problem 10.66 is false.

Bludov's example takes a simple linearly ordered group $G$ and nontrivial proper convex subgroups
$A$ and $B$. Conjugates of convex subgroups are convex and the convex subgroups form a chain, so
$A \cdot gBg^{-1}$ and $gBg^{-1} \cdot A$ both equal the larger of $A$ and $gBg^{-1}$, and
$AB \ne G$. Such subgroups exist: a nontrivial simple ordered group is not archimedean
(archimedean ordered groups are abelian, by Hölder), so it has nontrivial proper convex subgroups.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 10.66 (A. N.
Fomin, V. P. Shunkov); resolution: V. V. Bludov, letter of 12 February 1997, recorded in the
Kourovka Archive, Problem 10.66, Archive answer: "No; for example, for G being any simple linearly
ordered group and A and B arbitrary proper convex subgroups of G".
-/
public theorem permutingConjugatesNotSimple_refuted : ¬ permutingConjugatesNotSimple := by
  intro h
  have hv : (⟨vPerm, vPerm_mem⟩ : boundedAut) ∈ fixNeg := fun x hx =>
    pl_suppIn (by norm_num) (by norm_num) x (Or.inl hx)
  have hne : fixNeg ≠ ⊥ := by
    intro hb
    rw [hb] at hv
    exact vPerm_ne_one (congrArg Subtype.val ((Subgroup.mem_bot).mp hv))
  let w : boundedAut := ⟨plPerm (-2) 0 (-1) (-3 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num), plPerm_mem _ _ _ _⟩
  have hw : w ∉ fixNeg := by
    intro hw
    have := hw (-1) (by norm_num)
    simp only [w, plPerm_apply] at this
    rw [pl_apply_self (by norm_num)] at this
    norm_num at this
  refine h boundedAut fixNeg fixNeg hne hne ?_ ?_ boundedAut_isSimpleGroup
  · rw [(coe_mul_of_le (le_refl fixNeg)).1]
    intro hu
    exact hw (by rw [← SetLike.mem_coe, hu]; trivial)
  · intro g
    rcases fixNeg_comparable g with hle | hle
    · rw [(coe_mul_of_le hle).1, (coe_mul_of_le hle).2]
    · rw [(coe_mul_of_le hle).1, (coe_mul_of_le hle).2]

end MathlibExt.GroupTheory.PermutingConjugatesSimpleGroupKourovka10Problem66Wanted
