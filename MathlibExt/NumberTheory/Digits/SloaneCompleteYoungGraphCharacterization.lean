/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.GCD.Basic
public import MathlibExt.NumberTheory.Digits.CompleteYoungGraph
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.LinearCombination

/-! # Characterization of complete Young graphs

We prove Kendrick's gcd criterion by counting the diagonal carry pairs in a complete Young graph.
-/

namespace MetaMathlibExt
namespace sloane_complete_young_graph_characterization

private theorem modulus_factor (k : ℕ) : k ^ 2 - 1 = (k - 1) * (k + 1) := by
  simpa [mul_comm] using (Nat.sq_sub_sq k 1)

private theorem modulus_pos {k : ℕ} (hk : 2 ≤ k) : 0 < k ^ 2 - 1 := by
  rw [modulus_factor]
  exact Nat.mul_pos (by omega) (by omega)

private theorem modulus_add_one {k : ℕ} (hk : 2 ≤ k) : k ^ 2 - 1 + 1 = k * k := by
  have h := modulus_pos hk
  rw [pow_two] at *
  omega

private theorem mul_k_mul_k_modEq {k : ℕ} (hk : 2 ≤ k) (x : ℕ) :
    k * (k * x) ≡ x [MOD k ^ 2 - 1] := by
  rw [← mul_assoc, ← modulus_add_one hk, add_mul, one_mul]
  exact Nat.ModEq.modulus_mul_add

-- Eliminate the second digit from the two carry equations.
private theorem carry_eq {g k r s t u a b : ℕ} (hk : 2 ≤ k)
    (h₁ : k * b + s = a + u * g) (h₂ : k * a + t = b + r * g) :
    (k ^ 2 - 1) * a + (k * t + s) = u * g + k * (r * g) := by
  linear_combination k * h₂ + h₁ + a * modulus_add_one hk

private theorem carry_mod {g k r s t u a b : ℕ} (hk : 2 ≤ k)
    (h₁ : k * b + s = a + u * g) (h₂ : k * a + t = b + r * g) :
    k * t + s ≡ u * g + k * (r * g) [MOD k ^ 2 - 1] :=
  (Nat.ModEq.modulus_mul_add (m := k ^ 2 - 1) (a := a) (b := k * t + s)).symm.trans
    (carry_eq hk h₁ h₂ ▸ Nat.ModEq.rfl)

private theorem edge_unique {g k : ℕ} (hk : 2 ≤ k) {source : Option (Fin k × Fin k)}
    {target : Fin k × Fin k} {d e : Fin g × Fin g}
    (hd : IsYoungCarryEdge source target d) (he : IsYoungCarryEdge source target e) : d = e := by
  have hd' := carry_eq hk hd.2.1 hd.2.2
  have he' := carry_eq hk he.2.1 he.2.2
  rw [← he'] at hd'
  have ha := Nat.eq_of_mul_eq_mul_left (modulus_pos hk) (Nat.add_right_cancel hd')
  -- The second carry equation determines the second digit once the first is fixed.
  have h₂ := hd.2.2
  rw [ha, he.2.2] at h₂
  exact Prod.ext (Fin.ext ha) (Fin.ext (Nat.add_right_cancel h₂.symm))

private theorem diagonal_dvd_iff {g k r : ℕ} (hkg : k < g) :
    (k ^ 2 - 1 ∣ (g - k) * r) ↔ k * r ≡ r * g [MOD k ^ 2 - 1] := by
  have hle : k * r ≤ r * g := by rw [mul_comm r g]; exact Nat.mul_le_mul_right r hkg.le
  rw [Nat.modEq_iff_dvd' hle, mul_comm r g, ← Nat.sub_mul]

-- If a carry pair is adjacent to both the start and zero, its two squares are
-- congruent modulo k² - 1. Both squares are smaller than that modulus.
private theorem diagonal_of_edges {g k : ℕ} (hk : 2 ≤ k) (hkg : k < g)
    {v : Fin k × Fin k} {z : Fin k} (hz : z.val = 0)
    {d e : Fin g × Fin g} (hd : IsYoungCarryEdge none v d)
    (he : IsYoungCarryEdge (some v) (z, z) e) :
    v.1 = v.2 ∧ (k ^ 2 - 1 ∣ (g - k) * v.1.val) := by
  have h₁ : k * v.1.val ≡ v.2.val * g [MOD k ^ 2 - 1] := by
    simpa using carry_mod hk hd.2.1 hd.2.2
  have h₂ : v.2.val ≡ k * (v.1.val * g) [MOD k ^ 2 - 1] := by
    simpa [hz] using carry_mod hk he.2.1 he.2.2
  have h₁' : v.1.val ≡ k * (v.2.val * g) [MOD k ^ 2 - 1] :=
    (mul_k_mul_k_modEq hk _).symm.trans (h₁.mul_left k)
  have hs : v.1.val * v.1.val ≡ v.2.val * v.2.val [MOD k ^ 2 - 1] :=
    (h₁'.mul_right _).trans (by simpa [mul_comm, mul_left_comm, mul_assoc] using
      (h₂.mul_right v.2.val).symm)
  have hbound (r : Fin k) : r.val * r.val < k ^ 2 - 1 := by
    have hr : r.val ≤ k - 1 := by have := r.isLt; omega
    have hlt : (k - 1) * (k - 1) < (k - 1) * (k + 1) :=
      Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    rw [modulus_factor]
    exact (Nat.mul_le_mul hr hr).trans_lt hlt
  have hv : v.1 = v.2 := Fin.ext <| mul_self_inj (Nat.zero_le _) (Nat.zero_le _) |>.mp
    (hs.eq_of_lt_of_lt (hbound _) (hbound _))
  exact ⟨hv, (diagonal_dvd_iff hkg).mpr (by simpa only [← hv] using h₁)⟩

-- The diagonal divisibility condition propagates along every edge when the
-- gcd exceeds the carry range. The start uses the same carries as zero.
private theorem diagonal_of_edge {g k : ℕ} (hk : 2 ≤ k) (hkg : k < g)
    (hgcd : k < Nat.gcd (g - k) (k ^ 2 - 1)) {r t u a b : ℕ}
    (ht : t < k) (hu : u < k) (hr : k ^ 2 - 1 ∣ (g - k) * r)
    (h₁ : k * b + r = a + u * g) (h₂ : k * a + t = b + r * g) :
    t = u ∧ (k ^ 2 - 1 ∣ (g - k) * t) := by
  have hr' : r ≡ k * (r * g) [MOD k ^ 2 - 1] :=
    (mul_k_mul_k_modEq hk r).symm.trans (((diagonal_dvd_iff hkg).mp hr).mul_left k)
  have htu : k * t ≡ u * g [MOD k ^ 2 - 1] := hr'.add_right_cancel (carry_mod hk h₁ h₂)
  let d := Nat.gcd (g - k) (k ^ 2 - 1)
  have hd : d ∣ k ^ 2 - 1 := Nat.gcd_dvd_right _ _
  have hg : k ≡ g [MOD d] := Nat.modEq_of_dvd' hkg.le (Nat.gcd_dvd_left _ _)
  have hkt : k * t ≡ k * u [MOD d] := (htu.of_dvd hd).trans (by
    simpa only [mul_comm g u, mul_comm k u] using (hg.symm.mul_left u))
  have htu' : t ≡ u [MOD d] :=
    ((mul_k_mul_k_modEq hk t).of_dvd hd).symm.trans
      ((hkt.mul_left k).trans ((mul_k_mul_k_modEq hk u).of_dvd hd))
  have heq := htu'.eq_of_lt_of_lt (ht.trans hgcd) (hu.trans hgcd)
  exact ⟨heq, (diagonal_dvd_iff hkg).mpr (heq ▸ htu)⟩

-- Write x_r = (g-k)r/(k²-1). The labels for [r,r] → [t,t] are
-- r + k x_r + x_t and t + x_r + k x_t.
private theorem diagonal_digits {g k r t : ℕ} (hk : 2 ≤ k) (hkg : k < g)
    (hrk : r < k) (htk : t < k)
    (hr : k ^ 2 - 1 ∣ (g - k) * r) (ht : k ^ 2 - 1 ∣ (g - k) * t) :
    ∃ d : Fin g × Fin g, (t ≠ 0 → d.1.val ≠ 0 ∧ d.2.val ≠ 0) ∧
      k * d.2.val + r = d.1.val + t * g ∧ k * d.1.val + t = d.2.val + r * g := by
  obtain ⟨x, hx⟩ := hr
  obtain ⟨y, hy⟩ := ht
  have hsub : g - k + k = g := Nat.sub_add_cancel hkg.le
  have hbound {v w : ℕ} (hv : v < k) (hw : (g - k) * v = (k ^ 2 - 1) * w) :
      w ≤ (g - k) / (k + 1) := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < k + 1)).mpr
    apply Nat.le_of_mul_le_mul_left _ (by omega : 0 < k - 1)
    calc
      (k - 1) * (w * (k + 1)) = (k ^ 2 - 1) * w := by rw [modulus_factor]; ac_rfl
      _ = (g - k) * v := hw.symm
      _ ≤ (k - 1) * (g - k) := by
        rw [mul_comm (k - 1)]
        exact Nat.mul_le_mul_left _ (by omega)
  have hlabel {v w z : ℕ} (hv : v < k)
      (hw : w ≤ (g - k) / (k + 1)) (hz : z ≤ (g - k) / (k + 1)) :
      v + k * w + z < g := by
    have hsum : k * w + z ≤ ((g - k) / (k + 1)) * (k + 1) := by
      calc
        k * w + z ≤ k * ((g - k) / (k + 1)) + (g - k) / (k + 1) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hw) hz
        _ = _ := by rw [Nat.mul_succ, mul_comm k]
    have hdiv := Nat.div_mul_le_self (g - k) (k + 1)
    omega
  refine ⟨(⟨r + k * x + y, hlabel hrk (hbound hrk hx) (hbound htk hy)⟩,
    ⟨t + k * y + x, hlabel htk (hbound htk hy) (hbound hrk hx)⟩), ?_, ?_, ?_⟩
  · intro ht0
    have hypos : 0 < y := by
      apply Nat.pos_of_ne_zero
      intro hy0
      have hpos := Nat.mul_pos (Nat.sub_pos_of_lt hkg) (Nat.pos_of_ne_zero ht0)
      simp [hy0] at hy
      omega
    exact ⟨by change r + k * x + y ≠ 0; omega, by change t + k * y + x ≠ 0; omega⟩
  · change k * (t + k * y + x) + r = r + k * x + y + t * g
    linear_combination t * hsub - hy - y * modulus_add_one hk
  · change k * (r + k * x + y) + t = t + k * y + x + r * g
    linear_combination r * hsub - hx - x * modulus_add_one hk

private theorem diagonal_carry_ncard {g k : ℕ} (hk : 2 ≤ k) :
    ({v : Fin k × Fin k | v.1 = v.2 ∧ (k ^ 2 - 1 ∣ (g - k) * v.1.val)}).ncard =
      Nat.gcd (g - k) (k ^ 2 - 1) / (k + 1) + 1 := by
  let D := k ^ 2 - 1
  let d := Nat.gcd (g - k) D
  let step := D / d
  have hD : 0 < D := modulus_pos hk
  have hd : d ∣ D := Nat.gcd_dvd_right _ _
  have hstep : 0 < step := Nat.div_pos (Nat.le_of_dvd hD hd) (Nat.gcd_pos_of_pos_right _ hD)
  have hprod : step * d = D := Nat.div_mul_cancel hd
  have hmultiple (r : ℕ) : (D ∣ (g - k) * r) ↔ step ∣ r := by
    constructor
    · intro hr
      have hmod : (g - k) * r ≡ (g - k) * 0 [MOD D] := by simpa using hr.modEq_zero_nat
      simpa only [Nat.gcd_comm D (g - k), Nat.modEq_zero_iff_dvd] using
        hmod.cancel_left_div_gcd hD
    · intro hr
      have hmul := Nat.mul_dvd_mul (Nat.gcd_dvd_left (g - k) D) hr
      rwa [mul_comm d step, hprod] at hmul
  have hratio : (k - 1) / step = d / (k + 1) := by
    calc
      (k - 1) / step = ((k - 1) * (k + 1)) / (step * (k + 1)) := by
        rw [Nat.mul_div_mul_right _ _ (by omega : 0 < k + 1)]
      _ = d / (k + 1) := by
        rw [← modulus_factor, ← show step * d = k ^ 2 - 1 from hprod,
          Nat.mul_div_mul_left _ _ hstep]
  let f (j : Fin ((k - 1) / step + 1)) : Fin k × Fin k :=
    let r : Fin k := ⟨j.val * step, by
      have hj : j.val ≤ (k - 1) / step := by have := j.isLt; omega
      have := (Nat.le_div_iff_mul_le hstep).mp hj
      omega⟩
    (r, r)
  have hf : Function.Injective f := by
    intro i j h
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right hstep (congrArg (fun v => v.1.val) h))
  have hset : {v : Fin k × Fin k | v.1 = v.2 ∧ (D ∣ (g - k) * v.1.val)} = Set.range f := by
    ext v
    constructor
    · rintro ⟨hv, hdvd⟩
      obtain ⟨j, hj⟩ := (hmultiple _).mp hdvd
      have hjle : j ≤ (k - 1) / step := by
        apply (Nat.le_div_iff_mul_le hstep).mpr
        rw [mul_comm, ← hj]
        have := v.1.isLt
        omega
      have he : (f ⟨j, by omega⟩).1 = v.1 := Fin.ext (by simpa [f, mul_comm] using hj.symm)
      exact ⟨⟨j, by omega⟩, Prod.ext he (he.trans hv)⟩
    · rintro ⟨j, rfl⟩
      exact ⟨rfl, (hmultiple _).mpr (dvd_mul_left _ _)⟩
  change ({v : Fin k × Fin k | v.1 = v.2 ∧ (D ∣ (g - k) * v.1.val)}).ncard = _
  rw [hset, Set.ncard_range_of_injective hf, Nat.card_fin, hratio]

end sloane_complete_young_graph_characterization

open sloane_complete_young_graph_characterization in
/-- **Characterization of complete Young graphs.** Let $g$, $k$ and $m$ be natural numbers with
$2 \le k < g$ and $m \ge 2$. Then the Young graph $Y(g, k)$ is complete on $m$ nodes if and only
if

$$\left\lfloor \frac{\gcd(g - k,\, k^2 - 1)}{k + 1} \right\rfloor = m - 1.$$

Source: Corollary at lines 574-576
(quotation span SHA-256
`a7c50f9bea3cb4b958aecdbee7b56879d930178eae594729d8e54e36b7767395`)
of L. H. Kendrick, "Young Graphs: 1089 et al.", Journal of Integer
Sequences 18 (2015), stable source URL
`https://cs.uwaterloo.ca/journals/JIS/VOL18/Kendrick/ken1.tex`
(frozen source SHA-256
`28568ffc708329fe2de23639f32fd9f7a24a772a043deb40f9098c0f82e465c2`,
stable source ID `jis_grounded_3014355e4f55ef0bb856bf6f`).
In the source's `K_m`
convention, the nodes other than the distinguished starting node form the
complete directed graph on `m` nodes, so the Young graph has `m + 1` total
nodes including that distinguished start; `[0, 0]` is one of the `m`
non-start nodes. Natural-number division represents the source floor
because all quantities are nonnegative and the denominator is positive.
The hypothesis is `2 ≤ m`, not `1 ≤ m`. The corollary rests on Theorem
`thm:completegraph`, whose proof starts "Since $s_1$ exists", so it needs
`m - 1 ≥ 1`. For `m = 1` the class `K_1` contains no Young graph: every Young
graph is connected and contains `[0, 0]`, so the starting node has an edge to
some node other than `[0, 0]` (proof of Theorem `thm:0iso`), while a graph in
`K_1` has none. With `1 ≤ m`, `(g, k) = (10, 9)` and `m = 1` give
`gcd(1, 80) / 10 = 0 = m - 1`, but `Y(10, 9)` is the 1089 graph, not in `K_1`. -/
public theorem sloane_complete_young_graph_characterization
    (g k m : Nat) (hk : 2 ≤ k) (hkg : k < g) (hm : 2 ≤ m) :
    IsCompleteYoungGraph g k m ↔
      Nat.gcd (g - k) (k ^ 2 - 1) / (k + 1) = m - 1 := by
  unfold IsCompleteYoungGraph
  extract_lets adj reaches pivot retained ordinary
  let zero : Fin k := ⟨0, by omega⟩
  let z : Fin k × Fin k := (zero, zero)
  let diagonal : Set (Fin k × Fin k) :=
    {v | v.1 = v.2 ∧ (k ^ 2 - 1 ∣ (g - k) * v.1.val)}
  let q := Nat.gcd (g - k) (k ^ 2 - 1) / (k + 1)
  have hz : z ∈ diagonal := ⟨rfl, by simp [z, zero]⟩
  have hcount : diagonal.ncard = q + 1 := diagonal_carry_ncard hk
  have zero_of_values (v : Fin k × Fin k) (h₁ : v.1.val = 0) (h₂ : v.2.val = 0) :
      v = z :=
    Prod.ext (Fin.ext h₁) (Fin.ext h₂)
  have ordinaryEdge {v w : Fin k × Fin k} (hv : v ∈ diagonal) (hw : w ∈ diagonal) :
      ∃! d : Fin g × Fin g, IsYoungCarryEdge (some v) w d := by
    obtain ⟨hv', hdv⟩ := hv
    obtain ⟨hw', hdw⟩ := hw
    obtain ⟨d, _, h₁, h₂⟩ :=
      diagonal_digits hk hkg v.1.isLt w.1.isLt hdv hdw
    have hd : IsYoungCarryEdge (some v) w d := by
      refine ⟨by simp, ?_, h₂⟩
      change k * d.2.val + v.2.val = d.1.val + w.2.val * g
      simpa only [← hv', ← hw'] using h₁
    exact ⟨d, hd, fun e he => edge_unique hk he hd⟩
  have startEdge {v : Fin k × Fin k} (hv : v ∈ diagonal) :
      adj none (some v) ↔ v ≠ z := by
    constructor
    · rintro ⟨d, hd⟩ rfl
      have he : (k ^ 2 - 1) * d.1.val = 0 := by
        simpa [z, zero] using carry_eq hk hd.2.1 hd.2.2
      exact (hd.1 rfl).1 ((Nat.mul_eq_zero.mp he).resolve_left (modulus_pos hk).ne')
    · intro hvz
      obtain ⟨hv', hdv⟩ := hv
      have hp : v.1.val ≠ 0 := fun h => hvz (zero_of_values v h (hv' ▸ h))
      obtain ⟨d, hpos, h₁, h₂⟩ := diagonal_digits hk hkg zero.isLt v.1.isLt hz.2 hdv
      refine ⟨d, fun _ => hpos hp, ?_, h₂⟩
      change k * d.2.val + 0 = d.1.val + v.2.val * g
      simpa only [← hv'] using h₁
  have hmem (hq : 0 < q) : ordinary = diagonal ∧ retained none := by
    have hgcd : k < Nat.gcd (g - k) (k ^ 2 - 1) := by
      have hle := (Nat.le_div_iff_mul_le (by omega : 0 < k + 1)).mp (show 1 ≤ q from hq)
      exact Nat.lt_of_succ_le (by simpa only [one_mul] using hle)
    have hclosed {u v : Option (Fin k × Fin k)}
        (hu : ∀ w, u = some w → w ∈ diagonal) (e : adj u v) :
        ∀ w, v = some w → w ∈ diagonal := by
      rintro w rfl
      obtain ⟨d, hd⟩ := e
      cases u with
      | none =>
        have h := diagonal_of_edge hk hkg hgcd w.1.isLt w.2.isLt (by simp : k ^ 2 - 1 ∣
          (g - k) * 0) hd.2.1 hd.2.2
        exact ⟨Fin.ext h.1, h.2⟩
      | some u =>
        have ⟨hu', hdu⟩ := hu u rfl
        have h₁ : k * d.2.val + u.1.val = d.1.val + w.2.val * g := by
          have h := hd.2.1
          change k * d.2.val + u.2.val = _ at h
          rwa [← hu'] at h
        have h := diagonal_of_edge hk hkg hgcd w.1.isLt w.2.isLt hdu h₁ hd.2.2
        exact ⟨Fin.ext h.1, h.2⟩
    have hreach {v : Option (Fin k × Fin k)} (hv : reaches none v) :
        ∀ w, v = some w → w ∈ diagonal := by
      induction hv with
      | refl => simp
      | tail _ e ih => exact hclosed ih e
    obtain ⟨w, hw, hwz⟩ := diagonal.exists_ne_of_one_lt_ncard (by rw [hcount]; omega) z
    have hreachw : reaches none (some w) := .single ((startEdge hw).mpr hwz)
    have hpivot {v : Fin k × Fin k} (hv : v ∈ diagonal) : pivot (some v) := Or.inl hv.1
    refine ⟨Set.Subset.antisymm (fun v hv => hreach hv.1 v rfl) ?_,
      ⟨.refl, Or.inr ⟨some w, hpivot hw, hreachw⟩⟩⟩
    intro v hv
    refine ⟨?_, Or.inl (hpivot hv)⟩
    obtain rfl | hvz := eq_or_ne v z
    · obtain ⟨d, hd, _⟩ := ordinaryEdge hw hz
      exact hreachw.tail ⟨d, hd⟩
    · exact .single ((startEdge hv).mpr hvz)
  change _ ↔ q = m - 1
  constructor
  · rintro ⟨_, _, _, hc, z', hzmem, hz₁, hz₂, hcomplete, hstart⟩
    obtain rfl := zero_of_values z' hz₁ hz₂
    obtain ⟨v, hv, hvz⟩ := ordinary.exists_ne_of_one_lt_ncard (by omega) z
    obtain ⟨d, hd⟩ := (hstart v hv).mpr hvz
    obtain ⟨e, he, _⟩ := hcomplete v hv z hzmem
    have hvd : v ∈ diagonal := diagonal_of_edges hk hkg rfl hd he
    have hq : 0 < q := by
      have hh : 1 < diagonal.ncard := (Set.one_lt_ncard_iff).mpr ⟨v, z, hvd, hz, hvz⟩
      omega
    rw [(hmem hq).1, hcount] at hc
    omega
  · intro hq
    obtain ⟨hs, hnone⟩ := hmem (by omega)
    refine ⟨hk, hkg, hnone, by rw [hs, hcount]; omega, z, hs ▸ hz, rfl, rfl, ?_, ?_⟩
    · rw [hs]
      exact fun _ hv _ hw => ordinaryEdge hv hw
    · rw [hs]
      exact fun _ hv => startEdge hv

end MetaMathlibExt
