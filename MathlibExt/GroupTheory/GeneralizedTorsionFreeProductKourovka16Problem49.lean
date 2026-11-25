/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.CoprodI
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Data.List.Rotate
import Mathlib.Data.Rat.Floor
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Order.Int.LeastGreatest
import Mathlib.Order.Interval.Set.IsoIoo
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith

/-!
# Generalized torsion in free products (Kourovka Notebook Problem 16.49)

Kourovka Notebook, Archive of Solved Problems, Problem 16.49 (V. M. Kopytov, N. Ya. Medvedev): is it
true that a free product of groups without generalized torsion is a group without generalized
torsion?

The theorem `freeProductNoGeneralizedTorsion_holds` answers this question affirmatively.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.49 (V. M.
Kopytov, N. Ya. Medvedev). UnsolvedMath record UM-00701241 (`KOU-16.49`), dataset
ulamai/UnsolvedMath v1.8.0.

Free products of arbitrary families of groups (`Monoid.CoprodI`), as in the problem and the
Archive's answer; Theorem 1.5 of the resolution is stated for finitely many factors. Generalized
torsion as in Problem 16.48 (`h ≠ 1` with a nonempty product of conjugates of `h` trivial).

## Proof

Under the hypotheses, a generalized torsion element projects to the identity in each factor.
A cyclically reduced counterexample must therefore have at least two syllables. Repeat its word
along the integer line, writing its syllables as $a_m$. We construct a free product action on copies
of the rational line indexed by the direct product of the factors. The action on the indices is
ordinary left multiplication by the projection to the direct product. Each syllable $a_m$ takes
height $m+1$ in every fibre to height $m$ in its image fibre, preserving the order within fibres.

To arrange this, give each factor its own coordinates in every fibre. In that factor's coordinates
the action changes only the fibre index. For a syllable $a_m$ in the factor, we place both
landmarks $m$ and $m+1$ in the interval $(m,m+1)$. Their positions are given by consecutive values
of an increasing function along the orbits of $a_m$, which are infinite. Cyclic reduction keeps
the pairs of landmarks for each factor disjoint. Linear interpolation extends the coordinates to
the whole rational line.

The word preserves each fibre and takes every multiple of its length to the preceding multiple.
It therefore moves every rational point strictly downwards. Its conjugates have the same property,
which rules out a nonempty product equal to the identity.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.GeneralizedTorsionFreeProductKourovka16Problem49Wanted

/-- **Generalized torsion element (Kourovka 16.49).** An element $h$ of a group $H$ is a generalized
torsion element when $h \ne 1$ and some nonempty product of conjugates of $h$ is trivial, that is,
$x_1^{-1} h x_1 \cdots x_k^{-1} h x_k = 1$ for some $k \ge 1$ and some $x_1, \dots, x_k \in H$. -/
def IsGeneralizedTorsion {H : Type*} [Group H] (h : H) : Prop :=
  h ≠ 1 ∧ ∃ l : List H, l ≠ [] ∧ (l.map fun x => x⁻¹ * h * x).prod = 1

/-- **Kopytov–Medvedev question on generalized torsion in free products (Kourovka 16.49).** The
statement that for every family of groups $(G_i)_{i \in I}$ none of which contains a generalized
torsion element (an element $h \ne 1$ such that some nonempty product of conjugates of $h$ is
trivial), the free product of the family contains no generalized torsion element either. -/
def freeProductNoGeneralizedTorsion : Prop :=
  ∀ (ι : Type) (G : ι → Type) [∀ i, Group (G i)],
    (∀ i, ∀ g : G i, ¬ IsGeneralizedTorsion g) → ∀ g : Monoid.CoprodI G, ¬ IsGeneralizedTorsion g

open Monoid CoprodI

/-- Interpolate a strictly increasing grid of rational landmarks with bounded displacement. -/
private theorem interpolate {v : ℤ → ℚ} (hv : StrictMono v)
    (hb : ∀ n : ℤ, (n : ℚ) - 1 ≤ v n ∧ v n ≤ n + 1) :
    ∃ e : ℚ ≃o ℚ, ∀ n : ℤ, e n = v n := by
  let f (x : ℚ) := v ⌊x⌋ + (x - ⌊x⌋) * (v (⌊x⌋ + 1) - v ⌊x⌋)
  have hstep (n : ℤ) : 0 < v (n + 1) - v n := sub_pos.mpr (hv (by omega))
  have hbounds (x : ℚ) : v ⌊x⌋ ≤ f x ∧ f x < v (⌊x⌋ + 1) := by
    have h0 := Int.floor_le x
    have h1 := Int.lt_floor_add_one x
    simp only [f]
    constructor
    · exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr h0) (hstep _).le)
    · nlinarith [mul_pos (by linarith : 0 < 1 - (x - ⌊x⌋)) (hstep ⌊x⌋)]
  have hmono : StrictMono f := by
    intro x y hxy
    by_cases h : ⌊x⌋ = ⌊y⌋
    · simp only [f]
      rw [h]
      gcongr
      exact hstep _
    · have h' : ⌊x⌋ + 1 ≤ ⌊y⌋ := by
        have := Int.floor_mono hxy.le
        omega
      exact ((hbounds x).2.trans_le (hv.monotone h')).trans_le (hbounds y).1
  have hsurj : Function.Surjective f := by
    intro y
    have hbt : ∀ k : ℤ, v k ≤ y → k ≤ ⌊y⌋ + 2 := by
      intro k hk
      have := (hb k).1
      have := Int.lt_floor_add_one y
      exact_mod_cast (show (k : ℚ) ≤ (⌊y⌋ : ℚ) + 2 by linarith)
    have hne : v (⌊y⌋ - 1) ≤ y := by
      have := (hb (⌊y⌋ - 1)).2
      push_cast at this
      linarith [Int.floor_le y]
    obtain ⟨n, hn, hmax⟩ := Int.exists_greatest_of_bdd ⟨_, hbt⟩ ⟨_, hne⟩
    have hnext : y < v (n + 1) := by
      by_contra! hc
      have := hmax _ hc
      omega
    let t := (y - v n) / (v (n + 1) - v n)
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hn) (hstep _).le
    have ht1 : t < 1 := (div_lt_one (hstep _)).mpr (by linarith)
    have hfl : ⌊(n : ℚ) + t⌋ = n := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
    refine ⟨n + t, ?_⟩
    simp only [f, hfl, add_sub_cancel_left, t, div_mul_cancel₀ _ (hstep n).ne']
    ring
  refine ⟨hmono.orderIsoOfSurjective f hsurj, ?_⟩
  intro n
  change f (n : ℚ) = v n
  simp [f]

/-- On each orbit of left multiplication by `a`, use the exponent as an increasing coordinate. -/
private theorem increasing_coordinate {A : Type*} [Group A] (a : A)
    (ha : orderOf a = 0) : ∃ v : A → ℚ,
      (∀ k, 0 < v k ∧ v k < 1) ∧ ∀ k, v k < v (a * k) := by
  let H := Subgroup.zpowers a
  let rep (k : A) := (QuotientGroup.mk (s := H) k⁻¹).out
  have hrep (k : A) : k * rep k ∈ H := by
    have h := Quotient.out_eq (QuotientGroup.mk (s := H) k⁻¹)
    have := QuotientGroup.eq.mp h
    simpa [rep] using H.inv_mem this
  choose h hh using fun k => (Subgroup.mem_zpowers_iff.mp (hrep k))
  have hinj : Function.Injective (fun n : ℤ => a ^ n) :=
    injective_zpow_iff_not_isOfFinOrder.mpr (orderOf_eq_zero_iff.mp ha)
  have hsucc (k : A) : h (a * k) = h k + 1 := by
    have he : (QuotientGroup.mk (s := H) (a * k)⁻¹) = QuotientGroup.mk (s := H) k⁻¹ := by
      apply QuotientGroup.eq.mpr
      simp [mul_assoc, H]
    have hr : rep (a * k) = rep k := congrArg Quotient.out he
    apply hinj
    change a ^ h (a * k) = a ^ (h k + 1)
    rw [add_comm (h k), zpow_add, zpow_one, hh, hh, hr, mul_assoc]
  let b (n : ℤ) : ℚ := ((orderIsoIooNegOneOne ℚ (n : ℚ) : ℚ) + 1) / 2
  refine ⟨fun k => b (h k), fun k => ?_, fun k => ?_⟩
  · have bounds := (orderIsoIooNegOneOne ℚ (h k : ℚ)).2
    dsimp [b]
    constructor <;> linarith [bounds.1, bounds.2]
  · change b (h k) < b (h (a * k))
    rw [hsucc]
    have hlt := (orderIsoIooNegOneOne ℚ).strictMono
      (show (h k : ℚ) < ((h k + 1 : ℤ) : ℚ) by simp)
    change (_ : ℚ) < _ at hlt
    dsimp [b]
    linarith

section LineAction

variable {ι : Type} {G : ι → Type}
private abbrev Coordinates (G : ι → Type) := ∀ i, G i

local notation "K" => Coordinates G
local notation "X" => (K × ℚ)

private def below (x y : X) : Prop := x.1 = y.1 ∧ x.2 < y.2

private theorem below_trans {x y z : X} (h : below x y) (h' : below y z) : below x z :=
  ⟨h.1.trans h'.1, h.2.trans h'.2⟩

variable [∀ i, Group (G i)] [DecidableEq ι]

/-- Transport left multiplication on fibre indices through the coordinate systems for factor `i`. -/
private def factorAction (e : ι → K → ℚ ≃o ℚ) (i : ι) : G i →* Equiv.Perm X where
  toFun a := Equiv.prodShear (Equiv.mulLeft (Pi.mulSingle i a)) fun k =>
    (e i k).toEquiv.trans (e i (Pi.mulSingle i a * k)).symm.toEquiv
  map_one' := by ext ⟨k, q⟩ <;> simp [Equiv.prodShear]
  map_mul' a b := by
    ext ⟨k, q⟩ <;> simp [Equiv.prodShear, Equiv.Perm.mul_apply, Pi.mulSingle_mul, mul_assoc]

private theorem factorAction_apply (e : ι → K → ℚ ≃o ℚ) (i : ι) (a : G i) (k : K) (q : ℚ) :
    factorAction e i a (k, q) =
      (Pi.mulSingle i a * k, (e i (Pi.mulSingle i a * k)).symm (e i k q)) := rfl

private theorem preserves_below (e : ι → K → ℚ ≃o ℚ) (g : CoprodI G) {x y : X}
    (h : below x y) : below (lift (factorAction e) g x) (lift (factorAction e) g y) := by
  induction g using CoprodI.induction_on generalizing x y with
  | one => simpa using h
  | of i a =>
    obtain ⟨k, u⟩ := x
    obtain ⟨k', v⟩ := y
    obtain ⟨rfl : k = k', huv⟩ := h
    simp only [lift_of, factorAction_apply]
    exact ⟨rfl, ((e i _).symm.strictMono ((e i _).strictMono huv))⟩
  | mul a b ha hb => simpa [Equiv.Perm.mul_apply] using ha (hb h)

private theorem project_first (e : ι → K → ℚ ≃o ℚ) (g : CoprodI G) (x : X) :
    (lift (factorAction e) g x).1 = lift (MonoidHom.mulSingle G) g * x.1 := by
  induction g using CoprodI.induction_on generalizing x with
  | one => simp
  | of i a => rfl
  | mul a b ha hb => simp [Equiv.Perm.mul_apply, ha, hb, mul_assoc]

private theorem choose_charts (A : ℤ → Σ i, G i)
    (hadj : ∀ m, (A (m - 1)).1 ≠ (A m).1)
    (hinf : ∀ m, orderOf (A m).2 = 0) :
    ∃ e : ι → K → ℚ ≃o ℚ, ∀ (m : ℤ) (k : K),
      factorAction e (A m).1 (A m).2 (k, (m + 1 : ℤ)) =
        (Pi.mulSingle (A m).1 (A m).2 * k, (m : ℚ)) := by
  choose u hu hinc using fun m => increasing_coordinate (A m).2 (hinf m)
  let v (m : ℤ) (k : K) := u m (k (A m).1)
  let step (m : ℤ) (k : K) := Pi.mulSingle (A m).1 (A m).2 * k
  have hv (m : ℤ) (k : K) : 0 < v m k ∧ v m k < 1 := hu m _
  have hs (m : ℤ) (k : K) : v m k < v m (step m k) := by simpa [v, step] using hinc m (k _)
  -- For a syllable of factor i at position m, its two endpoints use the same interval.
  let grid (i : ι) (k : K) (m : ℤ) : ℚ :=
    if (A (m - 1)).1 = i then (m - 1 : ℤ) + v (m - 1) (step (m - 1) k) else m + v m k
  have mono (i : ι) (k : K) : StrictMono (grid i k) := by
    apply strictMono_int_of_lt_succ
    intro m
    simp only [grid, add_sub_cancel_right, Int.cast_sub, Int.cast_one, Int.cast_add]
    split_ifs with hp hc hc
    · exact False.elim ((hadj m) (hp.trans hc.symm))
    · linarith [(hv (m - 1) (step (m - 1) k)).2, (hv (m + 1) k).1]
    · linarith [hs m k]
    · linarith [(hv m k).2, (hv (m + 1) k).1]
  have bounds (i : ι) (k : K) (m : ℤ) : (m : ℚ) - 1 ≤ grid i k m ∧ grid i k m ≤ m + 1 := by
    simp only [grid, Int.cast_sub, Int.cast_one]
    split <;> constructor <;> linarith [(hv m k).1, (hv m k).2, (hv (m - 1) (step (m - 1) k)).1,
      (hv (m - 1) (step (m - 1) k)).2]
  choose e he using fun i k => interpolate (mono i k) (bounds i k)
  refine ⟨e, fun m k => ?_⟩
  rw [factorAction_apply, Prod.mk.injEq]
  refine ⟨rfl, (e _ _).toEquiv.symm_apply_eq.mpr ?_⟩
  change e _ k ((m + 1 : ℤ) : ℚ) = e _ _ (m : ℚ)
  simp only [he]
  simp [grid, hadj]
  rfl

private def evalWord (l : List (Σ i, G i)) : CoprodI G :=
  (l.map fun a => of a.2).prod

private theorem period_action (e : ι → K → ℚ ≃o ℚ) (A : ℤ → Σ i, G i)
    (he : ∀ (m : ℤ) (k : K), factorAction e (A m).1 (A m).2 (k, (m + 1 : ℤ)) =
        (Pi.mulSingle (A m).1 (A m).2 * k, (m : ℚ)))
    (l : List (Σ i, G i)) (b : ℤ) (hl : ∀ (j : ℕ) (hj : j < l.length), l[j] = A (b + j))
    (k : K) :
    (lift (factorAction e) (evalWord l) (k, (b + l.length : ℤ))).2 = (b : ℚ) := by
  induction l generalizing b k with
  | nil => simp [evalWord]
  | cons a l ih =>
    have ha := hl 0 (by simp)
    change a = A (b + (0 : ℕ)) at ha
    simp only [Nat.cast_zero, add_zero] at ha
    have ht (j : ℕ) (hj : j < l.length) : l[j] = A (b + 1 + j) := by
      have hh := hl (j + 1) (by simp [hj])
      change l[j] = A (b + ((j + 1 : ℕ) : ℤ)) at hh
      simpa [add_assoc, add_comm 1 (j : ℤ)] using hh
    let x := lift (factorAction e) (evalWord l) (k, (b + 1 + l.length : ℤ))
    have hx : x = (x.1, ((b + 1 : ℤ) : ℚ)) := Prod.ext rfl (ih _ ht k)
    have hb : b + (a :: l).length = (b + 1 + l.length : ℤ) := by simp; ring
    rw [hb]
    change (lift (factorAction e) (of a.2 * evalWord l) _).2 = _
    rw [map_mul, Equiv.Perm.mul_apply, lift_of]
    change (factorAction e a.1 a.2 x).2 = _
    rw [hx, ha, he]

private theorem excludes_witness (e : ι → K → ℚ ≃o ℚ) {g : CoprodI G}
    (hdrop : ∀ x : X, below (lift (factorAction e) g x) x) : ¬ IsGeneralizedTorsion g := by
  rintro ⟨_, l, hl, hprod⟩
  let f := lift (factorAction e)
  have hc (a : CoprodI G) (x : X) : below (f (a⁻¹ * g * a) x) x := by
    have := preserves_below e a⁻¹ (hdrop (f a x))
    simpa [f, Equiv.Perm.mul_apply] using this
  have hall (w : List (CoprodI G)) (hw : w ≠ []) (x : X) :
      below (f ((w.map fun a => a⁻¹ * g * a).prod) x) x := by
    induction w generalizing x with
    | nil => contradiction
    | cons a t ih =>
      cases t with
      | nil => simpa using hc a x
      | cons b s =>
        rw [List.map_cons, List.prod_cons, map_mul, Equiv.Perm.mul_apply]
        exact below_trans (hc _ _) (ih (by simp) x)
  have h := hall l hl (1, 0)
  rw [hprod, map_one] at h
  exact (lt_irrefl (0 : ℚ)) h.2

private theorem map_witness {A B : Type*} [Group A] [Group B] (f : A →* B) {a : A}
    (h : IsGeneralizedTorsion a) (hne : f a ≠ 1) : IsGeneralizedTorsion (f a) := by
  obtain ⟨_, l, hne', hl⟩ := h
  refine ⟨hne, l.map f, by simpa, ?_⟩
  simpa [map_list_prod, List.map_map, Function.comp_def] using congrArg f hl

private theorem projection_eq_one (hG : ∀ i, ∀ a : G i, ¬ IsGeneralizedTorsion a)
    {g : CoprodI G} (hg : IsGeneralizedTorsion g) : lift (MonoidHom.mulSingle G) g = 1 := by
  ext i
  by_contra hn
  exact hG i _ (map_witness ((Pi.evalMonoidHom G i).comp (lift (MonoidHom.mulSingle G))) hg hn)

omit [DecidableEq ι] in
private theorem mixed_case (hG : ∀ i, ∀ a : G i, ¬ IsGeneralizedTorsion a)
    (l : List (Σ i, G i)) (hn : 0 < l.length)
    (A : ℤ → Σ i, G i) (hadj : ∀ m, (A (m - 1)).1 ≠ (A m).1)
    (hinf : ∀ m, orderOf (A m).2 = 0)
    (hperiod : ∀ (b : ℤ) (j : ℕ) (hj : j < l.length), l[j] = A (b * l.length + j)) :
    ¬ IsGeneralizedTorsion (evalWord l) := by
  classical
  intro hg
  obtain ⟨e, he⟩ := choose_charts A hadj hinf
  let f := lift (factorAction e)
  have hfirst (x : X) : (f (evalWord l) x).1 = x.1 := by
    simpa [projection_eq_one hG hg] using project_first e (evalWord l) x
  have hgrid (k : K) (b : ℤ) :
      f (evalWord l) (k, ((b + 1) * l.length : ℤ)) = (k, ((b * l.length : ℤ) : ℚ)) := by
    apply Prod.ext
    · exact hfirst _
    simpa [add_mul] using period_action e A he l (b * l.length) (hperiod b) k
  apply excludes_witness e _ hg
  rintro ⟨k, q⟩
  refine ⟨hfirst _, ?_⟩
  let n : ℚ := l.length
  have hpos : 0 < n := by dsimp [n]; exact_mod_cast hn
  let b := ⌊q / n⌋
  have hlo : (b : ℚ) * n ≤ q := (le_div_iff₀ hpos).mp (Int.floor_le _)
  have hhi : q < ((b : ℚ) + 1) * n := (div_lt_iff₀ hpos).mp (Int.lt_floor_add_one _)
  have hh : below (k, q) (k, ((b + 1) * l.length : ℤ)) :=
    ⟨rfl, by push_cast; exact hhi⟩
  have := preserves_below e (evalWord l) hh
  change below (f _ _) (f _ _) at this
  rw [hgrid] at this
  exact this.2.trans_le (by push_cast; exact hlo)

omit [DecidableEq ι] in
private theorem rotated_witness {l : List (Σ i, G i)} (hg : IsGeneralizedTorsion (evalWord l))
    (p : ℕ) (hp : p ≤ l.length) : IsGeneralizedTorsion (evalWord (l.rotate p)) := by
  let u := evalWord (l.take p)
  let v := evalWord (l.drop p)
  have huv : evalWord l = u * v := by
    rw [← List.take_append_drop p l]
    simp only [evalWord, List.map_append, List.prod_append]
    rfl
  have hvu : evalWord (l.rotate p) = v * u := by
    simp [List.rotate_eq_drop_append_take hp, evalWord, v, u]
  have he : MulAut.conj u⁻¹ (evalWord l) = evalWord (l.rotate p) := by
    rw [huv, hvu, MulAut.conj_apply]
    group
  rw [← he]
  apply map_witness (MulAut.conj u⁻¹).toMonoidHom hg
  exact fun h => hg.1 ((map_eq_one_iff _ (MulAut.conj u⁻¹).injective).mp h)

omit [DecidableEq ι] in
private theorem infinite_order (hG : ∀ i, ∀ a : G i, ¬ IsGeneralizedTorsion a)
    {i : ι} {a : G i} (ha : a ≠ 1) : orderOf a = 0 := by
  by_contra h
  apply hG i a
  refine ⟨ha, List.replicate (orderOf a) 1, ?_, by simp⟩
  simpa only [ne_eq, List.replicate_eq_nil_iff] using h

omit [DecidableEq ι] in
private theorem word_case (hG : ∀ i, ∀ a : G i, ¬ IsGeneralizedTorsion a)
    (l : List (Σ i, G i)) : ¬ IsGeneralizedTorsion (evalWord l) := by
  classical
  induction hlen : l.length using Nat.strong_induction_on generalizing l with
  | ind n ih =>
    intro hg
    have shorter (t : List (Σ i, G i)) (ht : t.length < n) := ih t.length ht t rfl
    have hn : 1 < l.length := by
      cases l with
      | nil => exact (hg.1 rfl).elim
      | cons a t =>
        cases t with
        | nil =>
          have hp : a.2 = 1 := by
            simpa [evalWord] using congrFun (projection_eq_one hG hg) a.1
          exact (hg.1 (by simp [evalWord, hp])).elim
        | cons => simp
    -- Rotate each consecutive pair to the front. A unit or a repeated index shortens the word.
    have good (p : ℕ) (hp : p < l.length) :
        l[p].2 ≠ 1 ∧ l[p].1 ≠ (l[(p + 1) % l.length]'(Nat.mod_lt _ (by omega))).1 := by
      have hr := rotated_witness hg p hp.le
      have hrl := List.length_rotate l p
      have h0 := List.getElem_rotate l p 0 (by omega)
      have h1 := List.getElem_rotate l p 1 (by omega)
      simp only [zero_add, Nat.mod_eq_of_lt hp] at h0
      rw [add_comm 1 p] at h1
      cases he : l.rotate p with
      | nil => simp only [he, List.length_nil] at hrl; omega
      | cons a t =>
        cases t with
        | nil => simp only [he, List.length_cons, List.length_nil] at hrl; omega
        | cons b s =>
          rw [he] at hr hrl
          obtain ⟨i, a⟩ := a
          obtain ⟨j, b⟩ := b
          have e0 : (⟨i, a⟩ : Σ i, G i) = l[p] := by simpa [he] using h0
          have e1 : (⟨j, b⟩ : Σ i, G i) = l[(p + 1) % l.length]'(Nat.mod_lt _ (by omega)) := by
            simpa [he] using h1
          rw [← e0, ← e1]
          change a ≠ 1 ∧ i ≠ j
          simp only [List.length_cons] at hrl
          constructor
          · intro h
            rw [h] at hr
            apply shorter (⟨j, b⟩ :: s) (by simp only [List.length_cons]; omega)
            simpa [evalWord] using hr
          · rintro rfl
            apply shorter (⟨i, a * b⟩ :: s) (by simp only [List.length_cons]; omega)
            simpa [evalWord, mul_assoc] using hr
    let pos (m : ℤ) : Fin l.length :=
      ⟨(m % l.length).toNat, by
        have hb := Int.emod_lt_of_pos m (show 0 < (l.length : ℤ) by omega)
        omega⟩
    let A (m : ℤ) := l.get (pos m)
    apply mixed_case hG l (by omega) A _ _ _ hg
    · intro m
      have hm : (pos m).val = ((pos (m - 1)).val + 1) % l.length := by
        have hpos : 0 < (l.length : ℤ) := by omega
        have h := Int.emod_add_emod (m - 1) (l.length : ℤ) 1
        have hnon := Int.emod_nonneg (m - 1) hpos.ne'
        simpa only [pos, sub_add_cancel, Int.toNat_one, Int.toNat_natCast,
          Int.toNat_emod (by omega : 0 ≤ (m - 1) % l.length + 1) hpos.le,
          Int.toNat_add hnon (by decide : (0 : ℤ) ≤ 1)] using congrArg Int.toNat h.symm
      intro h
      apply (good (pos (m - 1)) (pos (m - 1)).isLt).2
      change l[(pos (m - 1)).val].1 = l[(pos m).val].1 at h
      simpa only [hm] using h
    · exact fun m => infinite_order hG (good (pos m) (pos m).isLt).1
    · intro b j hj
      have hcast : (j : ℤ) < l.length := by exact_mod_cast hj
      simp [A, pos, Int.emod_eq_of_lt (Int.natCast_nonneg j) hcast]

end LineAction

/--
**Free products of groups without generalized torsion have no generalized torsion.** For every
family of groups $(G_i)_{i \in I}$ none of which contains a generalized torsion element (an element
$h \ne 1$ such that some nonempty product of conjugates of $h$ is trivial), the free product of the
family contains no generalized torsion element.

The Kourovka Archive answers 16.49 "Yes, it is true", citing Ito, Motegi and Teragaito (2019),
whose Theorem 1.5 shows that a generalized torsion element of a free product
$G_1 \ast \cdots \ast G_n$ of torsion-free groups is conjugate to a generalized torsion element of
some factor.

Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.49 (V. M. Kopytov, N.
Ya. Medvedev); resolution: T. Ito, K. Motegi and M. Teragaito, Generalized torsion and decomposition
of 3-manifolds, Proc. Amer. Math. Soc. 147 (2019), no. 11, 4999-5008, arXiv:1811.07532, Theorem 1.5
(a generalized torsion element of a free product G_1 ∗ ⋯ ∗ G_n of torsion-free groups is conjugate
to a generalized torsion element of some factor); Kourovka Archive, Problem 16.49 (Yes; moreover the
generalized torsion in a free product of torsion-free groups is conjugate to a generalized torsion
of one of its factor groups), https://arxiv.org/abs/1811.07532.
-/
public theorem freeProductNoGeneralizedTorsion_holds : freeProductNoGeneralizedTorsion := by
  classical
  intro ι G _ hG g
  have hw := (Word.equiv (M := G)).symm_apply_apply g
  exact hw ▸ word_case hG (Word.equiv g).toList

end MathlibExt.GroupTheory.GeneralizedTorsionFreeProductKourovka16Problem49Wanted
