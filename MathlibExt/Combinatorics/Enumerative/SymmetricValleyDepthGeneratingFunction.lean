/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.Enumerative.SymmetricPeaksCompositions
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Topology.Instances.Int
import Mathlib.Tactic.LinearCombination

/-!
# Generating function for symmetric valley depths in compositions

`MetaMathlibExt.symmetricValleyDepthSum_compositions_genFun` gives the ordinary generating
function for the sum of all valley depths. A distinguished valley of depth `d` and middle
part `b` occupies weight `3 * b + 2 * d`. The parts before and after it form two arbitrary
compositions.
-/

open PowerSeries PowerSeries.WithPiTopology

namespace MetaMathlibExt
namespace symmetricValleyDepthSum_compositions_genFun

-- Encode positive parts by their predecessors, so every word represents a composition.
private def parts (w : List ℕ) : List ℕ := w.map Nat.succ

private def word {n : ℕ} (c : Composition n) : List ℕ := c.blocks.map Nat.pred

private theorem parts_word {n : ℕ} (c : Composition n) : parts (word c) = c.blocks := by
  simp only [parts, word, List.map_map]
  conv_rhs => rw [← List.map_id c.blocks]
  apply List.map_congr_left
  intro a ha
  have := c.blocks_pos ha
  exact Nat.succ_pred_eq_of_pos this

private noncomputable def term (z : ℤ) (w : List ℕ) : ℤ⟦X⟧ :=
  C z * X ^ (parts w).sum

private noncomputable def series (f : List ℕ → ℤ) : ℤ⟦X⟧ :=
  mk fun n => ∑ c : Composition n, f (word c)

/-- Regroup all words by the sum of their positive parts. Each coefficient has finite support. -/
private theorem hasSum_words (f : List ℕ → ℤ) :
    HasSum (fun w => term (f w) w) (series f) := by
  apply (hasSum_iff_hasSum_coeff ℤ).mpr
  intro n
  have hinj : Function.Injective (@word n) := fun c e h =>
    Composition.ext (by simpa only [parts_word] using congrArg parts h)
  apply (hinj.hasSum_iff ?_).mp
  · simpa [Function.comp_def, term, parts_word, coeff_C_mul_X_pow, series] using
      hasSum_fintype (fun c : Composition n => f (word c))
  · intro w hw
    rw [term, coeff_C_mul_X_pow, ite_eq_right (fun h => hw ?_)]
    let c : Composition n := ⟨parts w, by simp [parts], h.symm⟩
    exact ⟨c, by simp [word, c, parts, List.map_map, Function.comp_def]⟩

private noncomputable def geom (k : ℕ) : ℤ⟦X⟧ := ∑' n : ℕ, (X ^ k : ℤ⟦X⟧) ^ n

private theorem hasSum_geom {k : ℕ} (hk : k ≠ 0) :
    HasSum (fun n : ℕ => (X ^ k : ℤ⟦X⟧) ^ n) (geom k) :=
  (summable_pow_of_constantCoeff_eq_zero (by simp [hk])).hasSum

private theorem geom_mul {k : ℕ} (hk : k ≠ 0) : geom k * (1 - X ^ k) = 1 :=
  tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp [hk])

-- The factor d in the valley weight gives the series 1 + 2x² + 3x⁴ + ⋯.
private noncomputable def depthTerm (d : ℕ) : ℤ⟦X⟧ :=
  C ((d : ℤ) + 1) * (X ^ 2) ^ d

private theorem summable_depthTerm : Summable depthTerm := by
  apply (summable_iff_summable_coeff ℤ).mpr
  intro n
  apply summable_of_hasFiniteSupport
  refine (Set.finite_Iic n).subset ?_
  intro d hd
  change coeff n (depthTerm d) ≠ 0 at hd
  rw [depthTerm, ← pow_mul, coeff_C_mul_X_pow] at hd
  split at hd <;> simp_all [Set.mem_Iic]
  omega

private theorem depthTerm_mul : (∑' d, depthTerm d) * (1 - X ^ 2) ^ 2 = 1 := by
  have step (d : ℕ) : depthTerm (d + 1) =
      depthTerm d * X ^ 2 + (X ^ 2 : ℤ⟦X⟧) ^ d * X ^ 2 := by
    simp [depthTerm, pow_succ, add_mul, mul_assoc]
  have h := summable_depthTerm.tsum_eq_zero_add
  simp_rw [step] at h
  rw [((summable_depthTerm.mul_right _).tsum_add
    ((hasSum_geom (k := 2) (by decide)).summable.mul_right _)),
    summable_depthTerm.tsum_mul_right, (hasSum_geom (k := 2) (by decide)).summable.tsum_mul_right]
    at h
  change (∑' d, depthTerm d) = depthTerm 0 + ((∑' d, depthTerm d) * X ^ 2 + geom 2 * X ^ 2) at h
  rw [show depthTerm 0 = 1 by simp [depthTerm]] at h
  linear_combination (1 - X ^ 2) * h + X ^ 2 * geom_mul (k := 2) (by decide)

/-- Restrict the sum to a parametrization of the words on which the statistic can be nonzero. -/
private theorem hasSum_indexed {ι : Type*} (f : List ℕ → ℤ) (idx : ι → List ℕ)
    (hi : Function.Injective idx) (hzero : ∀ w ∉ Set.range idx, f w = 0) :
    HasSum (fun i => term (f (idx i)) (idx i)) (series f) :=
  (hi.hasSum_iff (fun w hw => by simp [hzero w hw, term])).mpr (hasSum_words f)

private def tailStat (f : List ℕ → ℤ) : List ℕ → ℤ
  | [] => 0
  | _ :: w => f w

/-- Prepending one positive part multiplies the series by `x / (1 - x)`. -/
private theorem series_tailStat (f : List ℕ → ℤ) :
    series (tailStat f) = geom 1 * X * series f := by
  let idx (p : ℕ × List ℕ) := p.1 :: p.2
  have hs := hasSum_indexed (tailStat f) idx (by
    rintro ⟨a, w⟩ ⟨b, t⟩ h
    simpa [idx, Prod.ext_iff] using h) (by
    rintro (_ | ⟨a, w⟩) hw
    · rfl
    · exact (hw ⟨(a, w), rfl⟩).elim)
  have h := hs.prod_fiberwise (g := fun a => X ^ (a + 1) * series f) fun a => by
    simpa [idx, tailStat, term, parts, pow_add, mul_left_comm] using
      (hasSum_words f).mul_left (X ^ (a + 1))
  exact h.unique (by simpa [pow_succ] using
    (((hasSum_geom (k := 1) (by decide)).mul_right X).mul_right (series f)))

private noncomputable def count : ℤ⟦X⟧ := series fun _ => 1

private theorem count_mul : count * (1 - 2 * X) = 1 - X := by
  have hc (n : ℕ) : coeff n count = (2 : ℤ) ^ (n - 1) := by
    simp [count, series, composition_card]
  rw [mul_sub, mul_one, show count * (2 * X) = (count + count) * X by ring]
  ext n
  cases n with
  | zero => simpa using hc 0
  | succ n =>
    rw [map_sub, coeff_succ_mul_X, map_add, hc, hc, map_sub]
    cases n <;> simp [coeff_one, coeff_X, pow_succ]
    ring

/-- Depth contributed by a valley in the first three positions, in predecessor coordinates. -/
private def initial : List ℕ → ℤ
  | a :: b :: c :: _ => if a = c then ((a - b : ℕ) : ℤ) else 0
  | _ => 0

private def valleyWord (p : (ℕ × ℕ) × List ℕ) : List ℕ :=
  let (b, d) := p.1
  (b + d + 1) :: b :: (b + d + 1) :: p.2

private theorem series_initial :
    series initial = geom 3 * (∑' d, depthTerm d) * (X ^ 5 * count) := by
  have hs := hasSum_indexed initial valleyWord (by
    rintro ⟨⟨b, d⟩, w⟩ ⟨⟨c, e⟩, t⟩ h
    simp only [valleyWord, List.cons.injEq] at h
    obtain ⟨h, rfl, _, rfl⟩ := h
    congr 2
    omega) (by
    rintro (_ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩) hw <;> try rfl
    by_cases h : a = c ∧ b < a
    · obtain ⟨rfl, h⟩ := h
      have ha : b + (a - b - 1) + 1 = a := by omega
      exact (hw ⟨((b, a - b - 1), t), by simp [valleyWord, ha]⟩).elim
    · simp only [initial]
      split <;> simp_all [Nat.sub_eq_zero_of_le])
  have h := hs.prod_fiberwise
    (g := fun p => ((X ^ 3) ^ p.1 * depthTerm p.2 * X ^ 5) * count) fun ⟨b, d⟩ => by
      apply ((hasSum_words (fun _ => 1)).mul_left
        ((X ^ 3) ^ b * depthTerm d * X ^ 5)).congr_fun
      intro w
      have hsize : (parts (valleyWord ((b, d), w))).sum =
          3 * b + 2 * d + 5 + (parts w).sum := by
        simp only [valleyWord, parts, List.map_cons, List.sum_cons]
        omega
      change term (initial (valleyWord ((b, d), w))) (valleyWord ((b, d), w)) = _
      rw [term, hsize]
      simp only [valleyWord, initial, ↓reduceIte, show b + d + 1 - b = d + 1 by omega,
        Nat.cast_add, Nat.cast_one, depthTerm, term, map_one, one_mul, pow_add, pow_mul]
      ring
  have h' := h.prod_fiberwise
    (g := fun b => ((X ^ 3) ^ b * (∑' d, depthTerm d)) * (X ^ 5 * count)) fun b => by
      simpa only [mul_assoc] using
        ((summable_depthTerm.hasSum.mul_left ((X ^ 3) ^ b)).mul_right (X ^ 5 * count))
  exact h'.unique (((hasSum_geom (k := 3) (by decide)).mul_right _).mul_right _)

private def depth (w : List ℕ) : ℤ := symmetricValleyDepthSum (parts w)

private theorem depth_eq (w : List ℕ) : depth w = tailStat depth w + initial w := by
  match w with
  | [] | [_] | [_, _] => simp [depth, parts, tailStat, initial, symmetricValleyDepthSum]
  | a :: b :: c :: t =>
    simp only [depth, parts, List.map_cons, symmetricValleyDepthSum, tailStat, initial,
      Nat.succ.injEq, Nat.succ_lt_succ_iff, Nat.succ_sub_succ_eq_sub, Nat.cast_add]
    split_ifs <;> simp_all
    omega

private theorem series_depth_mul :
    series depth * (1 - 2 * X) = series initial * (1 - X) := by
  have h : series depth = series (tailStat depth) + series initial := by
    ext n
    simp only [map_add, series, coeff_mk, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => depth_eq (word c)
  rw [series_tailStat] at h
  have hg : geom 1 * (1 - X) = 1 := by simpa using geom_mul (k := 1) (by decide)
  linear_combination (1 - X) * h + X * series depth * hg

end symmetricValleyDepthSum_compositions_genFun

open symmetricValleyDepthSum_compositions_genFun in
/-- **Generating function for the total depth of symmetric valleys over compositions.** For
$n \ge 0$, let $\operatorname{dsv}(n)$ be the sum, over all compositions $c$ of $n$, of the total
depth of the symmetric valleys of the sequence of parts of $c$. Then in the ring $\mathbb{Z}[[x]]$
of formal power series,
$$\Big(\sum_{n \ge 0} \operatorname{dsv}(n)\, x^n\Big)(1-2x)^2(1-x^3)(1-x^2)^2 = x^5 - 2x^6 + x^7,$$
that is, $\sum_{n \ge 0} \operatorname{dsv}(n)\, x^n$ equals
$(x^5 - 2x^6 + x^7)/((1-2x)^2(1-x^3)(1-x^2)^2)$.

Source: Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of
Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65,
Lemma 2, (11) (`integers-2026-A65-lem-2`). -/
public theorem symmetricValleyDepthSum_compositions_genFun :
    PowerSeries.mk (fun n => ((∑ c : Composition n, symmetricValleyDepthSum c.blocks : ℕ) : ℤ)) *
        ((1 - 2 * X) ^ 2 * (1 - X ^ 3) * (1 - X ^ 2) ^ 2) = X ^ 5 - 2 * X ^ 6 + X ^ 7 := by
  have hD : PowerSeries.mk
      (fun n => ((∑ c : Composition n, symmetricValleyDepthSum c.blocks : ℕ) : ℤ)) =
      series depth := by
    ext n
    simp [series, depth, parts_word]
  rw [hD]
  have hi : series initial * ((1 - X ^ 3) * (1 - X ^ 2) ^ 2) = X ^ 5 * count := by
    rw [series_initial]
    calc
      _ = (geom 3 * (1 - X ^ 3)) * ((∑' d, depthTerm d) * (1 - X ^ 2) ^ 2) *
          (X ^ 5 * count) := by ring
      _ = _ := by rw [geom_mul (by decide), depthTerm_mul, one_mul, one_mul]
  linear_combination (1 - 2 * X) * (1 - X ^ 3) * (1 - X ^ 2) ^ 2 * series_depth_mul +
    (1 - X) * (1 - 2 * X) * hi + X ^ 5 * (1 - X) * count_mul

end MetaMathlibExt
