/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterFourBridgeEndpointZero
import Code.Ising.LebowitzPfisterLowFaceCertificate





open Finset

namespace StatMech.Ising
open StatMech.FrontierA
open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace LowFaceCertificate

def TriTerm.eval (t : TriTerm) (x y z : Real) : Real :=
  t.coeff * x ^ t.ex * y ^ t.ey * z ^ t.ez

def evalTerms : List TriTerm -> Real -> Real -> Real -> Real
  | [], _, _, _ => 0
  | t :: ts, x, y, z => t.eval x y z + evalTerms ts x y z

def TriPoly.eval (p : TriPoly) (x y z : Real) : Real :=
  evalTerms p.terms x y z

lemma evalTerms_insert (t : TriTerm) (ts : List TriTerm) (x y z : Real) :
    evalTerms (TriPoly.insert t ts) x y z =
      t.eval x y z + evalTerms ts x y z := by
  induction ts with
  | nil => simp [TriPoly.insert, evalTerms]
  | cons s ss ih =>
      simp only [TriPoly.insert]
      split_ifs with h
      · rcases h with ⟨hx, hy, hz⟩
        simp only [evalTerms, TriTerm.eval]
        rw [hx, hy, hz]
        push_cast
        ring
      · simp [evalTerms, ih]
        ring

lemma evalTerms_foldl_insert (out ts : List TriTerm) (x y z : Real) :
    evalTerms (ts.foldl (fun acc t => TriPoly.insert t acc) out) x y z =
      evalTerms out x y z + evalTerms ts x y z := by
  induction ts generalizing out with
  | nil => simp [evalTerms]
  | cons t ts ih =>
      rw [List.foldl_cons, ih, evalTerms_insert]
      simp [evalTerms]
      ring

@[simp] lemma eval_ofTerms (ts : List TriTerm) (x y z : Real) :
    (TriPoly.ofTerms ts).eval x y z = evalTerms ts x y z := by
  simp [TriPoly.eval, TriPoly.ofTerms, evalTerms_foldl_insert, evalTerms]

@[simp] lemma eval_const (q : Int) (x y z : Real) :
    (TriPoly.const q).eval x y z = q := by
  simp [TriPoly.const, TriPoly.eval, evalTerms, TriTerm.eval]

lemma evalTerms_negMap (ts : List TriTerm) (x y z : Real) :
    evalTerms (ts.map fun t => { t with coeff := -t.coeff }) x y z =
      -evalTerms ts x y z := by
  induction ts with
  | nil => norm_num [evalTerms]
  | cons t ts ih =>
      simp [evalTerms, TriTerm.eval, ih]
      ring

@[simp] lemma eval_neg (p : TriPoly) (x y z : Real) :
    (-p).eval x y z = -p.eval x y z := by
  exact evalTerms_negMap p.terms x y z

lemma evalTerms_append (ps qs : List TriTerm) (x y z : Real) :
    evalTerms (ps ++ qs) x y z =
      evalTerms ps x y z + evalTerms qs x y z := by
  induction ps with
  | nil => simp [evalTerms]
  | cons t ts ih => simp [evalTerms, ih]; ring

@[simp] lemma eval_add (p q : TriPoly) (x y z : Real) :
    (p + q).eval x y z = p.eval x y z + q.eval x y z := by
  rw [show p + q = TriPoly.ofTerms (p.terms ++ q.terms) from rfl, eval_ofTerms]
  exact evalTerms_append p.terms q.terms x y z

@[simp] lemma eval_sub (p q : TriPoly) (x y z : Real) :
    (p - q).eval x y z = p.eval x y z - q.eval x y z := by
  change (p + -q).eval x y z = _
  rw [eval_add, eval_neg]
  rfl

@[simp] lemma eval_zero (x y z : Real) :
    (0 : TriPoly).eval x y z = 0 := by
  rw [show (0 : TriPoly) = TriPoly.const 0 by rfl, eval_const]
  norm_num
@[simp] lemma eval_one (x y z : Real) :
    (1 : TriPoly).eval x y z = 1 := by
  rw [show (1 : TriPoly) = TriPoly.const 1 by rfl, eval_const]
  norm_num
@[simp] lemma eval_two (x y z : Real) :
    (2 : TriPoly).eval x y z = 2 := by
  rw [show (2 : TriPoly) = TriPoly.const 2 by rfl, eval_const]
  norm_num
@[simp] lemma eval_three (x y z : Real) :
    (3 : TriPoly).eval x y z = 3 := by
  rw [show (3 : TriPoly) = TriPoly.const 3 by rfl, eval_const]
  norm_num
@[simp] lemma eval_six (x y z : Real) :
    (6 : TriPoly).eval x y z = 6 := by
  rw [show (6 : TriPoly) = TriPoly.const 6 by rfl, eval_const]
  norm_num
@[simp] lemma eval_nine (x y z : Real) :
    (9 : TriPoly).eval x y z = 9 := by
  rw [show (9 : TriPoly) = TriPoly.const 9 by rfl, eval_const]
  norm_num
@[simp] lemma eval_1764 (x y z : Real) :
    (1764 : TriPoly).eval x y z = 1764 := by
  rw [show (1764 : TriPoly) = TriPoly.const 1764 by rfl, eval_const]
  norm_num

lemma evalTerms_mulMap (s : TriTerm) (ts : List TriTerm) (x y z : Real) :
    evalTerms (ts.map fun t =>
      { ex := s.ex + t.ex, ey := s.ey + t.ey, ez := s.ez + t.ez,
        coeff := s.coeff * t.coeff }) x y z =
      s.eval x y z * evalTerms ts x y z := by
  induction ts with
  | nil => simp [evalTerms]
  | cons t ts ih =>
      simp [evalTerms, TriTerm.eval, ih, pow_add]
      ring

lemma evalTerms_mulFlatMap (ss ts : List TriTerm) (x y z : Real) :
    evalTerms (ss.flatMap fun s => ts.map fun t =>
      { ex := s.ex + t.ex, ey := s.ey + t.ey, ez := s.ez + t.ez,
        coeff := s.coeff * t.coeff }) x y z =
      evalTerms ss x y z * evalTerms ts x y z := by
  induction ss with
  | nil => simp [evalTerms]
  | cons s ss ih =>
      rw [List.flatMap_cons, evalTerms_append, evalTerms_mulMap, ih]
      rw [evalTerms]
      ring

@[simp] lemma eval_mul (p q : TriPoly) (x y z : Real) :
    (p * q).eval x y z = p.eval x y z * q.eval x y z := by
  rw [show p * q = TriPoly.ofTerms (p.terms.flatMap fun s =>
    q.terms.map fun t =>
      { ex := s.ex + t.ex, ey := s.ey + t.ey, ez := s.ez + t.ez,
        coeff := s.coeff * t.coeff }) from rfl,
    eval_ofTerms, evalTerms_mulFlatMap]
  rfl

@[simp] lemma eval_pow (p : TriPoly) (n : Nat) (x y z : Real) :
    (p ^ n).eval x y z = p.eval x y z ^ n := by
  induction n with
  | zero =>
      change (TriPoly.const 1).eval x y z = 1
      simpa only [Int.cast_one] using eval_const 1 x y z
  | succ n ih =>
      rw [show p ^ (n + 1) = p * p ^ n from rfl, eval_mul, ih, pow_succ]
      ring

def bernsteinWeight (n i : Nat) (x : Real) : Real :=
  n.choose i * x ^ i * (1 - x) ^ (n - i)

lemma bernsteinWeight_nonneg {n i : Nat} {x : Real}
    (hx0 : 0 <= x) (hx1 : x <= 1) :
    0 <= bernsteinWeight n i x := by
  unfold bernsteinWeight
  positivity

set_option maxHeartbeats 800000 in
lemma scaledBernFactor_sum_twelve (e : Nat) (he : e <= 6) (x : Real) :
    ∑ i : Fin 13,
      (scaledBernFactor 12 27720 e i : Real) * bernsteinWeight 12 i x =
      27720 * x ^ e := by
  interval_cases e <;>
    norm_num [Fin.sum_univ_succ, scaledBernFactor, bernsteinWeight, Nat.choose] <;>
    ring

set_option maxHeartbeats 800000 in
lemma scaledBernFactor_sum_seven (e : Nat) (he : e <= 6) (x : Real) :
    ∑ i : Fin 8,
      (scaledBernFactor 7 105 e i : Real) * bernsteinWeight 7 i x =
      105 * x ^ e := by
  interval_cases e <;>
    norm_num [Fin.sum_univ_succ, scaledBernFactor, bernsteinWeight, Nat.choose] <;>
    ring

set_option maxHeartbeats 800000 in
lemma scaledBernFactor_sum_three (e : Nat) (he : e <= 3) (x : Real) :
    ∑ i : Fin 4,
      (scaledBernFactor 3 3 e i : Real) * bernsteinWeight 3 i x =
      3 * x ^ e := by
  interval_cases e <;>
    norm_num [Fin.sum_univ_succ, scaledBernFactor, bernsteinWeight, Nat.choose] <;>
    ring

def radialTermCoeff (t : TriTerm) (a : Fin 13) (b : Fin 8) (c : Fin 4) : Int :=
  t.coeff * scaledBernFactor 12 27720 t.ex a *
    scaledBernFactor 7 105 t.ey b * scaledBernFactor 3 3 t.ez c

def radialCoeffTerms : List TriTerm -> Fin 13 -> Fin 8 -> Fin 4 -> Int
  | [], _, _, _ => 0
  | t :: ts, a, b, c => radialTermCoeff t a b c + radialCoeffTerms ts a b c

lemma foldl_radialTermCoeff (ts : List TriTerm) (q : Int)
    (a : Fin 13) (b : Fin 8) (c : Fin 4) :
    ts.foldl (fun q t => q + radialTermCoeff t a b c) q =
      q + radialCoeffTerms ts a b c := by
  induction ts generalizing q with
  | nil => simp [radialCoeffTerms]
  | cons t ts ih =>
      rw [List.foldl_cons, ih]
      simp [radialCoeffTerms]
      ring

lemma radialBernCoeffOf_eq (p : TriPoly) (a : Fin 13) (b : Fin 8) (c : Fin 4) :
    radialBernCoeffOf p a b c = radialCoeffTerms p.terms a b c := by
  rw [radialBernCoeffOf, show
    (fun q t => q + t.coeff * scaledBernFactor 12 27720 t.ex a *
      scaledBernFactor 7 105 t.ey b * scaledBernFactor 3 3 t.ez c) =
    (fun q t => q + radialTermCoeff t a b c) by rfl,
    foldl_radialTermCoeff]
  simp

def bernsteinEvalTerms (ts : List TriTerm) (r q h : Real) : Real :=
  ∑ a : Fin 13, ∑ b : Fin 8, ∑ c : Fin 4,
    (radialCoeffTerms ts a b c : Real) *
      bernsteinWeight 12 a r * bernsteinWeight 7 b q * bernsteinWeight 3 c h

lemma radialTerm_bernstein_sum (t : TriTerm) (r q h : Real)
    (hex : t.ex <= 6) (hey : t.ey <= 6) (hez : t.ez <= 3) :
    (∑ a : Fin 13, ∑ b : Fin 8, ∑ c : Fin 4,
      (radialTermCoeff t a b c : Real) *
        bernsteinWeight 12 a r * bernsteinWeight 7 b q * bernsteinWeight 3 c h) =
      (27720 * 105 * 3 : Real) * t.eval r q h := by
  have ha := scaledBernFactor_sum_twelve t.ex hex r
  have hb := scaledBernFactor_sum_seven t.ey hey q
  have hc := scaledBernFactor_sum_three t.ez hez h
  simp only [radialTermCoeff]
  push_cast
  calc
    (∑ a : Fin 13, ∑ b : Fin 8, ∑ c : Fin 4,
      (t.coeff : Real) * scaledBernFactor 12 27720 t.ex a *
        scaledBernFactor 7 105 t.ey b * scaledBernFactor 3 3 t.ez c *
        bernsteinWeight 12 a r * bernsteinWeight 7 b q * bernsteinWeight 3 c h) =
      ∑ a : Fin 13, ∑ b : Fin 8,
        ((t.coeff : Real) * scaledBernFactor 12 27720 t.ex a *
          bernsteinWeight 12 a r * scaledBernFactor 7 105 t.ey b *
          bernsteinWeight 7 b q) * (3 * h ^ t.ez) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        rw [← hc, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        ring
    _ = ∑ a : Fin 13,
        ((t.coeff : Real) * scaledBernFactor 12 27720 t.ex a *
          bernsteinWeight 12 a r) * (105 * q ^ t.ey) * (3 * h ^ t.ez) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [← hb, Finset.mul_sum]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b _
        ring
    _ = (t.coeff : Real) * (27720 * r ^ t.ex) *
        (105 * q ^ t.ey) * (3 * h ^ t.ez) := by
        rw [← ha, Finset.mul_sum]
        rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
    _ = (27720 * 105 * 3 : Real) * t.eval r q h := by
        simp only [TriTerm.eval]
        push_cast
        ring

lemma bernsteinEvalTerms_eq (ts : List TriTerm) (r q h : Real)
    (hbounds : ∀ t ∈ ts, t.ex <= 6 ∧ t.ey <= 6 ∧ t.ez <= 3) :
    bernsteinEvalTerms ts r q h =
      (27720 * 105 * 3 : Real) * evalTerms ts r q h := by
  induction ts with
  | nil => simp [bernsteinEvalTerms, radialCoeffTerms, evalTerms]
  | cons t ts ih =>
      have ht := hbounds t (by simp)
      have hts : ∀ s ∈ ts, s.ex <= 6 ∧ s.ey <= 6 ∧ s.ez <= 3 := by
        intro s hs
        exact hbounds s (by simp [hs])
      rw [show bernsteinEvalTerms (t :: ts) r q h =
        (∑ a : Fin 13, ∑ b : Fin 8, ∑ c : Fin 4,
          (radialTermCoeff t a b c : Real) *
            bernsteinWeight 12 a r * bernsteinWeight 7 b q * bernsteinWeight 3 c h) +
          bernsteinEvalTerms ts r q h by
        simp only [bernsteinEvalTerms, radialCoeffTerms]
        push_cast
        simp_rw [add_mul, Finset.sum_add_distrib],
        radialTerm_bernstein_sum t r q h ht.1 ht.2.1 ht.2.2,
        ih hts]
      rw [evalTerms]
      ring

lemma TriPoly.eval_nonneg_of_bernstein
    (p : TriPoly) (r q h : Real)
    (hr0 : 0 <= r) (hr1 : r <= 1)
    (hq0 : 0 <= q) (hq1 : q <= 1)
    (hh0 : 0 <= h) (hh1 : h <= 1)
    (hbounds : ∀ t ∈ p.terms, t.ex <= 6 ∧ t.ey <= 6 ∧ t.ez <= 3)
    (hcoeff : ∀ (a : Fin 13) (b : Fin 8) (c : Fin 4),
      0 <= radialBernCoeffOf p a b c) :
    0 <= p.eval r q h := by
  have hsum : 0 <= bernsteinEvalTerms p.terms r q h := by
    unfold bernsteinEvalTerms
    apply Finset.sum_nonneg
    intro a _
    apply Finset.sum_nonneg
    intro b _
    apply Finset.sum_nonneg
    intro c _
    rw [← radialBernCoeffOf_eq]
    have hcR : (0 : Real) <= radialBernCoeffOf p a b c := by
      exact_mod_cast hcoeff a b c
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hcR
          (bernsteinWeight_nonneg hr0 hr1))
        (bernsteinWeight_nonneg hq0 hq1))
      (bernsteinWeight_nonneg hh0 hh1)
  rw [bernsteinEvalTerms_eq p.terms r q h hbounds] at hsum
  norm_num at hsum ⊢
  simpa [TriPoly.eval] using hsum

theorem radializedCrossCoeff_eval_nonneg
    (i j k : Fin 8) (r q h : Real)
    (hr0 : 0 <= r) (hr1 : r <= 1)
    (hq0 : 0 <= q) (hq1 : q <= 1)
    (hh0 : 0 <= h) (hh1 : h <= 1) :
    0 <= (radialize (crossCoeffPoly i j k)).eval r q h := by
  apply TriPoly.eval_nonneg_of_bernstein _ r q h
    hr0 hr1 hq0 hq1 hh0 hh1
  · exact radializedCrossCoeff_bounds i j k
  · intro a b c
    exact radialBernCoeff_nonneg i j k a b c

def radialTermEval (t : TriTerm) (r q h : Real) : Real :=
  let degree := t.ex + t.ey + t.ez
  t.coeff * r ^ t.ex * q ^ (t.ex + t.ey) *
    h ^ (degree - 3) * (1 + q + r * q) ^ (6 - degree)

def radialEvalTerms : List TriTerm -> Real -> Real -> Real -> Real
  | [], _, _, _ => 0
  | t :: ts, r, q, h => radialTermEval t r q h + radialEvalTerms ts r q h

lemma evalTerms_radialFlatMap (ts : List TriTerm) (r q h : Real) :
    evalTerms (ts.flatMap fun t =>
      let degree := t.ex + t.ey + t.ez
      (TriPoly.const t.coeff * vx ^ t.ex * vy ^ (t.ex + t.ey) *
        vz ^ (degree - 3) * (1 + vy + vx * vy) ^ (6 - degree)).terms) r q h =
      radialEvalTerms ts r q h := by
  induction ts with
  | nil => simp [radialEvalTerms, evalTerms]
  | cons t ts ih =>
      rw [List.flatMap_cons, evalTerms_append, ih]
      change (TriPoly.const t.coeff * vx ^ t.ex * vy ^ (t.ex + t.ey) *
          vz ^ (t.ex + t.ey + t.ez - 3) *
          (1 + vy + vx * vy) ^ (6 - (t.ex + t.ey + t.ez))).eval r q h +
        radialEvalTerms ts r q h = radialEvalTerms (t :: ts) r q h
      simp only [eval_mul, eval_pow, eval_add, eval_const, eval_one]
      norm_num [vx, vy, vz, TriPoly.eval, evalTerms, TriTerm.eval]
      simp only [radialEvalTerms, radialTermEval]

lemma eval_radialize (p : TriPoly) (r q h : Real) :
    (radialize p).eval r q h = radialEvalTerms p.terms r q h := by
  rw [radialize, eval_ofTerms, evalTerms_radialFlatMap]

lemma radialTermEval_relation (t : TriTerm) (r q z : Real)
    (hlo : 3 <= t.ex + t.ey + t.ez)
    (hhi : t.ex + t.ey + t.ez <= 6) :
    z ^ 3 * radialTermEval t r q (z * (1 + q + r * q)) =
      (1 + q + r * q) ^ 3 * t.eval (r * q * z) (q * z) z := by
  let d := t.ex + t.ey + t.ez
  have hd0 : 3 + (d - 3) = d := by omega
  have hd1 : (d - 3) + (6 - d) = 3 := by omega
  have hd2 : t.ex + t.ey + t.ez = d := rfl
  let D : Real := 1 + q + r * q
  have hzpow : z ^ 3 * z ^ (d - 3) = z ^ d := by
    rw [← pow_add, hd0]
  have hDpow : D ^ (d - 3) * D ^ (6 - d) = D ^ 3 := by
    rw [← pow_add, hd1]
  have hqpow : q ^ (t.ex + t.ey) = q ^ t.ex * q ^ t.ey := by rw [pow_add]
  have hzsplit : z ^ d = z ^ t.ex * z ^ t.ey * z ^ t.ez := by
    rw [← hd2, pow_add, pow_add]
  simp only [radialTermEval, TriTerm.eval]
  rw [show 1 + q + r * q = D by rfl, mul_pow]
  calc
    z ^ 3 *
        ((t.coeff : Real) * r ^ t.ex * q ^ (t.ex + t.ey) *
          (z ^ (d - 3) * D ^ (d - 3)) * D ^ (6 - d)) =
      (t.coeff : Real) * r ^ t.ex * q ^ (t.ex + t.ey) *
        (z ^ 3 * z ^ (d - 3)) * (D ^ (d - 3) * D ^ (6 - d)) := by ring
    _ = (t.coeff : Real) * r ^ t.ex * (q ^ t.ex * q ^ t.ey) *
        (z ^ t.ex * z ^ t.ey * z ^ t.ez) * D ^ 3 := by
      rw [hzpow, hDpow, hqpow, hzsplit]
    _ = D ^ 3 *
        ((t.coeff : Real) * (r ^ t.ex * q ^ t.ex * z ^ t.ex) *
          (q ^ t.ey * z ^ t.ey) * z ^ t.ez) := by ring
    _ = D ^ 3 *
        ((t.coeff : Real) * (r * q * z) ^ t.ex *
          (q * z) ^ t.ey * z ^ t.ez) := by
      simp only [mul_pow]

lemma radialEvalTerms_relation (ts : List TriTerm) (r q z : Real)
    (hbounds : ∀ t ∈ ts,
      3 <= t.ex + t.ey + t.ez ∧ t.ex + t.ey + t.ez <= 6) :
    z ^ 3 * radialEvalTerms ts r q (z * (1 + q + r * q)) =
      (1 + q + r * q) ^ 3 * evalTerms ts (r * q * z) (q * z) z := by
  induction ts with
  | nil => simp [radialEvalTerms, evalTerms]
  | cons t ts ih =>
      have ht := hbounds t (by simp)
      have hts : ∀ s ∈ ts,
          3 <= s.ex + s.ey + s.ez ∧ s.ex + s.ey + s.ez <= 6 := by
        intro s hs
        exact hbounds s (by simp [hs])
      rw [radialEvalTerms, evalTerms]
      calc
        z ^ 3 *
            (radialTermEval t r q (z * (1 + q + r * q)) +
              radialEvalTerms ts r q (z * (1 + q + r * q))) =
          z ^ 3 * radialTermEval t r q (z * (1 + q + r * q)) +
            z ^ 3 * radialEvalTerms ts r q (z * (1 + q + r * q)) := by ring
        _ = (1 + q + r * q) ^ 3 * t.eval (r * q * z) (q * z) z +
            (1 + q + r * q) ^ 3 * evalTerms ts (r * q * z) (q * z) z := by
          rw [radialTermEval_relation t r q z ht.1 ht.2, ih hts]
        _ = (1 + q + r * q) ^ 3 *
            (t.eval (r * q * z) (q * z) z +
              evalTerms ts (r * q * z) (q * z) z) := by ring

lemma eval_radialize_relation (p : TriPoly) (r q z : Real)
    (hbounds : ∀ t ∈ p.terms,
      3 <= t.ex + t.ey + t.ez ∧ t.ex + t.ey + t.ez <= 6) :
    z ^ 3 * (radialize p).eval r q (z * (1 + q + r * q)) =
      (1 + q + r * q) ^ 3 * p.eval (r * q * z) (q * z) z := by
  rw [eval_radialize, radialEvalTerms_relation p.terms r q z hbounds]
  simp only [TriPoly.eval]





lemma TriPoly.eval_nonneg_of_radialize_relation
    (p : TriPoly) (r q z : Real)
    (hz : 0 <= z)
    (hD : 0 < 1 + q + r * q)
    (hbounds : ∀ t ∈ p.terms,
      3 <= t.ex + t.ey + t.ez ∧ t.ex + t.ey + t.ez <= 6)
    (hrad : 0 <= (radialize p).eval r q (z * (1 + q + r * q))) :
    0 <= p.eval (r * q * z) (q * z) z := by
  have hleft : 0 <= z ^ 3 *
      (radialize p).eval r q (z * (1 + q + r * q)) :=
    mul_nonneg (pow_nonneg hz 3) hrad
  rw [eval_radialize_relation p r q z hbounds] at hleft
  exact nonneg_of_mul_nonneg_right hleft (pow_pos hD 3)

def crossNumerator (x y z a b c : Real) : Real :=
  y * z * (x - x ^ 3 + y - y ^ 3 + z - z ^ 3) +
    9 * x * y * z * (x + y) * (1 - y) * a +
    9 * x * y * z * (x + z) * (1 - z) * b +
    9 * y ^ 2 * z * (y + z) * (1 - z) * c -
    3 * x * y * z * (3 - 2 * x) * (1 - y) * (1 - z) * (a * b) +
    6 * x ^ 2 * z * (1 - y) ^ 2 * (1 - z) * (a ^ 2 * b) +
    6 * x ^ 2 * y * (1 - y) * (1 - z) ^ 2 * (a * b ^ 2) -
    3 * x * y * z * (3 - 2 * y) * (1 - y) * (1 - z) * (a * c) +
    6 * x * y * z * (1 - y) ^ 2 * (1 - z) * (a ^ 2 * c) +
    6 * x * y ^ 2 * (1 - y) * (1 - z) ^ 2 * (a * c ^ 2) -
    3 * x * y ^ 2 * (3 - 2 * z) * (1 - z) ^ 2 * (b * c) +
    6 * x * y ^ 2 * (1 - z) ^ 3 * (b ^ 2 * c) +
    6 * x * y ^ 2 * (1 - z) ^ 3 * (b * c ^ 2)

lemma eval_crossCoeffPoly (i j k : Nat) (x y z : Real) :
    (crossCoeffPoly i j k).eval x y z =
      1764 * y * z * (x - x ^ 3 + y - y ^ 3 + z - z ^ 3) +
      (252 * i : Int) * (9 * x * y * z * (x + y) * (1 - y)) +
      (252 * j : Int) * (9 * x * y * z * (x + z) * (1 - z)) +
      (252 * k : Int) * (9 * y ^ 2 * z * (y + z) * (1 - z)) -
      (36 * i * j : Int) *
        (3 * x * y * z * (3 - 2 * x) * (1 - y) * (1 - z)) +
      (6 * i * (i - 1) * j : Int) *
        (6 * x ^ 2 * z * (1 - y) ^ 2 * (1 - z)) +
      (6 * j * (j - 1) * i : Int) *
        (6 * x ^ 2 * y * (1 - y) * (1 - z) ^ 2) -
      (36 * i * k : Int) *
        (3 * x * y * z * (3 - 2 * y) * (1 - y) * (1 - z)) +
      (6 * i * (i - 1) * k : Int) *
        (6 * x * y * z * (1 - y) ^ 2 * (1 - z)) +
      (6 * k * (k - 1) * i : Int) *
        (6 * x * y ^ 2 * (1 - y) * (1 - z) ^ 2) -
      (36 * j * k : Int) *
        (3 * x * y ^ 2 * (3 - 2 * z) * (1 - z) ^ 2) +
      (6 * j * (j - 1) * k : Int) * (6 * x * y ^ 2 * (1 - z) ^ 3) +
      (6 * k * (k - 1) * j : Int) * (6 * x * y ^ 2 * (1 - z) ^ 3) := by
  simp only [crossCoeffPoly]
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_neg, eval_const,
    eval_zero, eval_one, eval_two, eval_three, eval_six, eval_nine, eval_1764]
  norm_num [vx, vy, vz, TriPoly.eval, evalTerms, TriTerm.eval]

def bernsteinAverageSeven (x : Real) (f : Fin 8 -> Real) : Real :=
  ∑ i : Fin 8, bernsteinWeight 7 i x * f i

lemma bernsteinAverageSeven_const (x q : Real) :
    bernsteinAverageSeven x (fun _ => q) = q := by
  unfold bernsteinAverageSeven
  have h := scaledBernFactor_sum_seven 0 (by norm_num) x
  norm_num [scaledBernFactor, Nat.choose] at h
  calc
    bernsteinAverageSeven x (fun _ => q) =
        q / 105 * (∑ i : Fin 8, 105 * bernsteinWeight 7 i x) := by
      unfold bernsteinAverageSeven
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = q := by rw [h]; ring

lemma bernsteinAverageSeven_add (x : Real) (f g : Fin 8 -> Real) :
    bernsteinAverageSeven x (fun i => f i + g i) =
      bernsteinAverageSeven x f + bernsteinAverageSeven x g := by
  unfold bernsteinAverageSeven
  simp only [mul_add, Finset.sum_add_distrib]

lemma bernsteinAverageSeven_natCast_mul (x q : Real) :
    bernsteinAverageSeven x (fun i => q * i.val) = q * (7 * x) := by
  unfold bernsteinAverageSeven
  have h := scaledBernFactor_sum_seven 1 (by norm_num) x
  norm_num [scaledBernFactor, Nat.choose] at h
  calc
    bernsteinAverageSeven x (fun i => q * i.val) =
        q / 15 * (∑ i : Fin 8, (i.val : Real) * 15 * bernsteinWeight 7 i x) := by
      unfold bernsteinAverageSeven
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = q * (7 * x) := by rw [h]; ring

lemma bernsteinAverageSeven_falling_mul (x q : Real) :
    bernsteinAverageSeven x (fun i => q * (i.val * (i.val - 1) : Nat)) =
      q * (42 * x ^ 2) := by
  unfold bernsteinAverageSeven
  have h := scaledBernFactor_sum_seven 2 (by norm_num) x
  norm_num [scaledBernFactor, Nat.choose] at h
  calc
    bernsteinAverageSeven x (fun i => q * (i.val * (i.val - 1) : Nat)) =
        (2 * q) / 5 *
          (∑ i : Fin 8, (i.val.choose 2 : Real) * 5 * bernsteinWeight 7 i x) := by
      unfold bernsteinAverageSeven
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      fin_cases i <;> norm_num [Nat.choose] <;> ring
    _ = q * (42 * x ^ 2) := by rw [h]; ring

lemma bernsteinAverageSeven_choose_two_mul (x q : Real) :
    bernsteinAverageSeven x (fun i => q * i.val.choose 2) =
      q * (21 * x ^ 2) := by
  calc
    bernsteinAverageSeven x (fun i => q * i.val.choose 2) =
        bernsteinAverageSeven x
          (fun i => (q / 2) * (i.val * (i.val - 1) : Nat)) := by
      apply congrArg (bernsteinAverageSeven x)
      funext i
      fin_cases i <;> norm_num [Nat.choose] <;> ring
    _ = (q / 2) * (42 * x ^ 2) :=
      bernsteinAverageSeven_falling_mul x (q / 2)
    _ = q * (21 * x ^ 2) := by ring

def quadraticAverage (x : Real) (f : Fin 8 -> Real) : Real :=
  f 0 + 7 * x * (f 1 - f 0) +
    21 * x ^ 2 * (f 2 - 2 * f 1 + f 0)

lemma bernsteinAverageSeven_eq_quadraticAverage
    (x : Real) (f : Fin 8 -> Real)
    (hquad : ∀ i : Fin 8,
      f i = f 0 + i.val * (f 1 - f 0) +
        i.val.choose 2 * (f 2 - 2 * f 1 + f 0)) :
    bernsteinAverageSeven x f = quadraticAverage x f := by
  have hlin := bernsteinAverageSeven_natCast_mul x (f 1 - f 0)
  have hquad' := bernsteinAverageSeven_choose_two_mul x
    (f 2 - 2 * f 1 + f 0)
  calc
    bernsteinAverageSeven x f = bernsteinAverageSeven x
        (fun i => f 0 + i.val * (f 1 - f 0) +
          i.val.choose 2 * (f 2 - 2 * f 1 + f 0)) := by
      apply congrArg (bernsteinAverageSeven x)
      funext i
      exact hquad i
    _ = bernsteinAverageSeven x (fun _ => f 0) +
          bernsteinAverageSeven x (fun i => i.val * (f 1 - f 0)) +
          bernsteinAverageSeven x
            (fun i => i.val.choose 2 * (f 2 - 2 * f 1 + f 0)) := by
      rw [bernsteinAverageSeven_add, bernsteinAverageSeven_add]
    _ = f 0 + (f 1 - f 0) * (7 * x) +
          (f 2 - 2 * f 1 + f 0) * (21 * x ^ 2) := by
      rw [bernsteinAverageSeven_const,
        show bernsteinAverageSeven x (fun i => i.val * (f 1 - f 0)) =
          bernsteinAverageSeven x (fun i => (f 1 - f 0) * i.val) by
            apply congrArg (bernsteinAverageSeven x)
            funext i
            ring,
        hlin,
        show bernsteinAverageSeven x
            (fun i => i.val.choose 2 * (f 2 - 2 * f 1 + f 0)) =
          bernsteinAverageSeven x
            (fun i => (f 2 - 2 * f 1 + f 0) * i.val.choose 2) by
              apply congrArg (bernsteinAverageSeven x)
              funext i
              ring,
        hquad']
    _ = quadraticAverage x f := by
      unfold quadraticAverage
      ring

lemma quadraticAverage_preserves_quadratic
    (x : Real) (F : Fin 8 -> Fin 8 -> Real)
    (hquad : ∀ (i j : Fin 8),
      F i j = F 0 j + i.val * (F 1 j - F 0 j) +
        i.val.choose 2 * (F 2 j - 2 * F 1 j + F 0 j))
    (i : Fin 8) :
    quadraticAverage x (fun j => F i j) =
      quadraticAverage x (fun j => F 0 j) +
        i.val * (quadraticAverage x (fun j => F 1 j) -
          quadraticAverage x (fun j => F 0 j)) +
        i.val.choose 2 * (quadraticAverage x (fun j => F 2 j) -
          2 * quadraticAverage x (fun j => F 1 j) +
          quadraticAverage x (fun j => F 0 j)) := by
  unfold quadraticAverage
  simp only
  rw [hquad i 0, hquad i 1, hquad i 2]
  norm_num [Nat.choose]
  ring

set_option maxHeartbeats 10000000 in
theorem crossNumerator_bernstein_average
    (x y z a b c : Real) :
    bernsteinAverageSeven a (fun i =>
      bernsteinAverageSeven b (fun j =>
        bernsteinAverageSeven c (fun k =>
          (crossCoeffPoly i j k).eval x y z))) =
      1764 * crossNumerator x y z a b c := by
  let f : Fin 8 -> Fin 8 -> Fin 8 -> Real := fun i j k =>
    (crossCoeffPoly i j k).eval x y z
  have hf_k (i j k : Fin 8) :
      f i j k = f i j 0 + k.val * (f i j 1 - f i j 0) +
        k.val.choose 2 * (f i j 2 - 2 * f i j 1 + f i j 0) := by
    dsimp [f]
    simp only [eval_crossCoeffPoly]
    fin_cases k <;> norm_num [Nat.choose] <;> ring
  have hf_j (i j k : Fin 8) :
      f i j k = f i 0 k + j.val * (f i 1 k - f i 0 k) +
        j.val.choose 2 * (f i 2 k - 2 * f i 1 k + f i 0 k) := by
    dsimp [f]
    simp only [eval_crossCoeffPoly]
    fin_cases j <;> norm_num [Nat.choose] <;> ring
  have hf_i (i j k : Fin 8) :
      f i j k = f 0 j k + i.val * (f 1 j k - f 0 j k) +
        i.val.choose 2 * (f 2 j k - 2 * f 1 j k + f 0 j k) := by
    dsimp [f]
    simp only [eval_crossCoeffPoly]
    fin_cases i <;> norm_num [Nat.choose] <;> ring
  have hk (i j : Fin 8) :
      bernsteinAverageSeven c (fun k => f i j k) =
        quadraticAverage c (fun k => f i j k) := by
    apply bernsteinAverageSeven_eq_quadraticAverage
    exact hf_k i j
  have hj (i : Fin 8) :
      bernsteinAverageSeven b (fun j =>
        quadraticAverage c (fun k => f i j k)) =
      quadraticAverage b (fun j =>
        quadraticAverage c (fun k => f i j k)) := by
    apply bernsteinAverageSeven_eq_quadraticAverage
    intro j
    exact quadraticAverage_preserves_quadratic c
      (fun j k => f i j k) (hf_j i) j
  have hi :
      bernsteinAverageSeven a (fun i =>
        quadraticAverage b (fun j => quadraticAverage c (fun k => f i j k))) =
      quadraticAverage a (fun i =>
        quadraticAverage b (fun j => quadraticAverage c (fun k => f i j k))) := by
    apply bernsteinAverageSeven_eq_quadraticAverage
    intro i
    exact quadraticAverage_preserves_quadratic b
      (fun i j => quadraticAverage c (fun k => f i j k))
      (fun i j => quadraticAverage_preserves_quadratic c
        (fun i k => f i j k) (fun i k => hf_i i j k) i) i
  calc
    bernsteinAverageSeven a (fun i =>
        bernsteinAverageSeven b (fun j =>
          bernsteinAverageSeven c (fun k =>
            (crossCoeffPoly i j k).eval x y z))) =
      bernsteinAverageSeven a (fun i =>
        bernsteinAverageSeven b (fun j =>
          quadraticAverage c (fun k => f i j k))) := by
        apply congrArg (bernsteinAverageSeven a)
        funext i
        apply congrArg (bernsteinAverageSeven b)
        funext j
        exact hk i j
    _ = bernsteinAverageSeven a (fun i =>
        quadraticAverage b (fun j => quadraticAverage c (fun k => f i j k))) := by
      apply congrArg (bernsteinAverageSeven a)
      funext i
      exact hj i
    _ = quadraticAverage a (fun i =>
        quadraticAverage b (fun j => quadraticAverage c (fun k => f i j k))) := hi
    _ = 1764 * crossNumerator x y z a b c := by
      dsimp [quadraticAverage, f, crossNumerator]
      simp only [eval_crossCoeffPoly]
      norm_num
      ring

set_option maxHeartbeats 1000000 in
theorem crossCoeffPoly_eval_nonneg_ordered
    (i j k : Fin 8) {x y z : Real}
    (hx : 0 < x) (hxy : x <= y) (hyz : y <= z)
    (hsum : x + y + z <= 1) :
    0 <= (crossCoeffPoly i j k).eval x y z := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hz : 0 < z := lt_of_lt_of_le hy hyz
  let r := x / y
  let q := y / z
  let h := x + y + z
  have hr0 : 0 <= r := by positivity
  have hr1 : r <= 1 := (div_le_one hy).mpr hxy
  have hq0 : 0 <= q := by positivity
  have hq1 : q <= 1 := (div_le_one hz).mpr hyz
  have hh0 : 0 <= h := by dsimp [h]; positivity
  have hh1 : h <= 1 := hsum
  have hrad := radializedCrossCoeff_eval_nonneg i j k r q h
    hr0 hr1 hq0 hq1 hh0 hh1
  have hrqz : r * q * z = x := by
    dsimp [r, q]
    field_simp
  have hqz : q * z = y := by
    dsimp [q]
    field_simp
  have hzh : z * (1 + q + r * q) = h := by
    dsimp [r, q, h]
    field_simp
    ring
  have hd : 0 < 1 + q + r * q := by positivity
  have hp := TriPoly.eval_nonneg_of_radialize_relation
    (crossCoeffPoly i j k) r q z (le_of_lt hz) hd
      (crossCoeff_bounds i j k) (by
      rw [hzh]
      exact hrad)
  rw [hrqz, hqz] at hp
  exact hp

theorem crossNumerator_nonneg_ordered
    {x y z a b c : Real}
    (hx : 0 < x) (hxy : x <= y) (hyz : y <= z)
    (hsum : x + y + z <= 1)
    (ha0 : 0 <= a) (ha1 : a <= 1)
    (hb0 : 0 <= b) (hb1 : b <= 1)
    (hc0 : 0 <= c) (hc1 : c <= 1) :
    0 <= crossNumerator x y z a b c := by
  have havg : 0 <= bernsteinAverageSeven a (fun i =>
      bernsteinAverageSeven b (fun j =>
        bernsteinAverageSeven c (fun k =>
          (crossCoeffPoly i j k).eval x y z))) := by
    unfold bernsteinAverageSeven
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (bernsteinWeight_nonneg ha0 ha1) <| by
      apply Finset.sum_nonneg
      intro j _
      exact mul_nonneg (bernsteinWeight_nonneg hb0 hb1) <| by
        apply Finset.sum_nonneg
        intro k _
        exact mul_nonneg (bernsteinWeight_nonneg hc0 hc1)
          (crossCoeffPoly_eval_nonneg_ordered i j k hx hxy hyz hsum)
  rw [crossNumerator_bernstein_average] at havg
  nlinarith

set_option maxHeartbeats 1600000 in
theorem fourBridge_triangle_cross_remainder_nonneg_ordered_of_caps
    {x y z a b c : Real}
    (hx : 0 < x) (hxy : x <= y) (hyz : y <= z)
    (hsum : x ^ 2 + y ^ 2 + z ^ 2 <= 1)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c)
    (hacap : y * a <= (1 - y ^ 2) * x)
    (hbcap : z * b <= (1 - z ^ 2) * x)
    (hccap : z * c <= (1 - z ^ 2) * y) :
    0 <=
      x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) +
        z ^ 2 * (1 - z ^ 4) +
      9 * (a * x * y * (x ^ 2 + y ^ 2) +
        b * x * z * (x ^ 2 + z ^ 2) +
        c * y * z * (y ^ 2 + z ^ 2)) +
      6 * x * a * b * (x * y * z + y * b + z * a) +
      6 * y * a * c * (x * y * z + x * c + z * a) +
      6 * z * b * c * (x * y * z + x * c + y * b) -
      9 * (a * b * y * z + a * c * x * z + b * c * x * y) := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hz : 0 < z := lt_of_lt_of_le hy hyz
  have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx
  have hy2 : 0 < y ^ 2 := sq_pos_of_pos hy
  have hz2 : 0 < z ^ 2 := sq_pos_of_pos hz
  have hyv : 0 < 1 - y ^ 2 := by nlinarith [hz2]
  have hzv : 0 < 1 - z ^ 2 := by nlinarith [hx2]
  let A := y * a / ((1 - y ^ 2) * x)
  let B := z * b / ((1 - z ^ 2) * x)
  let C := z * c / ((1 - z ^ 2) * y)
  have hA0 : 0 <= A := by dsimp [A]; positivity
  have hA1 : A <= 1 := by
    dsimp [A]
    exact (div_le_one (mul_pos hyv hx)).mpr hacap
  have hB0 : 0 <= B := by dsimp [B]; positivity
  have hB1 : B <= 1 := by
    dsimp [B]
    exact (div_le_one (mul_pos hzv hx)).mpr hbcap
  have hC0 : 0 <= C := by dsimp [C]; positivity
  have hC1 : C <= 1 := by
    dsimp [C]
    exact (div_le_one (mul_pos hzv hy)).mpr hccap
  have hXY : x ^ 2 <= y ^ 2 := by nlinarith
  have hYZ : y ^ 2 <= z ^ 2 := by nlinarith
  have hcert := crossNumerator_nonneg_ordered
    (x := x ^ 2) (y := y ^ 2) (z := z ^ 2)
    (a := A) (b := B) (c := C)
    hx2 hXY hYZ hsum hA0 hA1 hB0 hB1 hC0 hC1
  have hid :
      crossNumerator (x ^ 2) (y ^ 2) (z ^ 2) A B C =
      y ^ 2 * z ^ 2 *
        (x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) +
          z ^ 2 * (1 - z ^ 4) +
        9 * (a * x * y * (x ^ 2 + y ^ 2) +
          b * x * z * (x ^ 2 + z ^ 2) +
          c * y * z * (y ^ 2 + z ^ 2)) +
        6 * x * a * b * (x * y * z + y * b + z * a) +
        6 * y * a * c * (x * y * z + x * c + z * a) +
        6 * z * b * c * (x * y * z + x * c + y * b) -
        9 * (a * b * y * z + a * c * x * z + b * c * x * y)) := by
    dsimp [A, B, C, crossNumerator]
    field_simp
    ring
  rw [hid] at hcert
  exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hcert)
    (mul_pos hy2 hz2)

set_option maxHeartbeats 1200000 in
theorem fourBridge_triangle_cross_remainder_nonneg_of_sqsum_le_one
    {x y z a b c : Real}
    (hx0 : 0 <= x) (hy0 : 0 <= y) (hz0 : 0 <= z)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hx1 : x <= 1) (hy1 : y <= 1) (hz1 : z <= 1)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c)
    (hxa : x * a ^ 2 <= (1 - x ^ 2) * y * a)
    (hya : y * a ^ 2 <= (1 - y ^ 2) * x * a)
    (hxb : x * b ^ 2 <= (1 - x ^ 2) * z * b)
    (hzb : z * b ^ 2 <= (1 - z ^ 2) * x * b)
    (hyc : y * c ^ 2 <= (1 - y ^ 2) * z * c)
    (hzc : z * c ^ 2 <= (1 - z ^ 2) * y * c)
    (hsum : x ^ 2 + y ^ 2 + z ^ 2 <= 1) :
    0 <=
      x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) +
        z ^ 2 * (1 - z ^ 4) +
      9 * (a * x * y * (x ^ 2 + y ^ 2) +
        b * x * z * (x ^ 2 + z ^ 2) +
        c * y * z * (y ^ 2 + z ^ 2)) +
      6 * x * a * b * (x * y * z + y * b + z * a) +
      6 * y * a * c * (x * y * z + x * c + z * a) +
      6 * z * b * c * (x * y * z + x * c + y * b) -
      9 * (a * b * y * z + a * c * x * z + b * c * x * y) := by
  have gxa := pair_covariance_square_bound_cancel hx0 hy0 hx1 ha hxa
  have gya := pair_covariance_square_bound_cancel hy0 hx0 hy1 ha hya
  have gxb := pair_covariance_square_bound_cancel hx0 hz0 hx1 hb hxb
  have gzb := pair_covariance_square_bound_cancel hz0 hx0 hz1 hb hzb
  have gyc := pair_covariance_square_bound_cancel hy0 hz0 hy1 hc hyc
  have gzc := pair_covariance_square_bound_cancel hz0 hy0 hz1 hc hzc
  rcases le_total x y with hxy | hyx
  · rcases le_total y z with hyz | hzy
    · exact fourBridge_triangle_cross_remainder_nonneg_ordered_of_caps
        hx hxy hyz hsum ha hb hc gya gzb gzc
    · rcases le_total x z with hxz | hzx
      · have h := fourBridge_triangle_cross_remainder_nonneg_ordered_of_caps
          hx hxz hzy (by nlinarith : x ^ 2 + z ^ 2 + y ^ 2 <= 1)
          hb ha hc gzb gya gyc
        convert h using 1 <;> ring
      · have h := fourBridge_triangle_cross_remainder_nonneg_ordered_of_caps
          hz hzx hxy (by nlinarith : z ^ 2 + x ^ 2 + y ^ 2 <= 1)
          hb hc ha gxb gyc gya
        convert h using 1 <;> ring
  · rcases le_total x z with hxz | hzx
    · have h := fourBridge_triangle_cross_remainder_nonneg_ordered_of_caps
        hy hyx hxz (by nlinarith : y ^ 2 + x ^ 2 + z ^ 2 <= 1)
        ha hc hb gxa gzc gzb
      convert h using 1 <;> ring
    · rcases le_total y z with hyz | hzy
      · have h := fourBridge_triangle_cross_remainder_nonneg_ordered_of_caps
          hy hyz hzx (by nlinarith : y ^ 2 + z ^ 2 + x ^ 2 <= 1)
          hc ha hb gzc gxa gxb
        convert h using 1 <;> ring
      · have h := fourBridge_triangle_cross_remainder_nonneg_ordered_of_caps
          hz hzy hyx (by nlinarith : z ^ 2 + y ^ 2 + x ^ 2 <= 1)
          hc hb ha gyc gxb gxa
        convert h using 1 <;> ring

theorem fourBridge_triangle_correct_nonneg_of_sqsum_le_one
    {x y z a b c : Real}
    (hx0 : 0 <= x) (hy0 : 0 <= y) (hz0 : 0 <= z)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hx1 : x <= 1) (hy1 : y <= 1) (hz1 : z <= 1)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c)
    (hxa : x * a ^ 2 <= (1 - x ^ 2) * y * a)
    (hya : y * a ^ 2 <= (1 - y ^ 2) * x * a)
    (hxb : x * b ^ 2 <= (1 - x ^ 2) * z * b)
    (hzb : z * b ^ 2 <= (1 - z ^ 2) * x * b)
    (hyc : y * c ^ 2 <= (1 - y ^ 2) * z * c)
    (hzc : z * c ^ 2 <= (1 - z ^ 2) * y * c)
    (hsum : x ^ 2 + y ^ 2 + z ^ 2 <= 1) :
    0 <=
      x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) +
        z ^ 2 * (1 - z ^ 4) +
      9 * (a * x * y * (x ^ 2 + y ^ 2) +
        b * x * z * (x ^ 2 + z ^ 2) +
        c * y * z * (y ^ 2 + z ^ 2)) +
      9 / 2 * (a ^ 2 * (x ^ 2 + y ^ 2) +
        b ^ 2 * (x ^ 2 + z ^ 2) + c ^ 2 * (y ^ 2 + z ^ 2)) +
      (-18 * a * b * y * z +
        6 * x * a * b * (x * y * z + y * b + z * a)) +
      (-18 * a * c * x * z +
        6 * y * a * c * (x * y * z + x * c + z * a)) +
      (-18 * b * c * x * y +
        6 * z * b * c * (x * y * z + x * c + y * b)) := by
  have hcross := fourBridge_triangle_cross_remainder_nonneg_of_sqsum_le_one
    hx0 hy0 hz0 hx hy hz hx1 hy1 hz1 ha hb hc
    hxa hya hxb hzb hyc hzc hsum
  have hsquares : 0 <= 9 / 2 *
      ((y * a - z * b) ^ 2 + (x * a - z * c) ^ 2 +
        (x * b - y * c) ^ 2) := by positivity
  have hid :
      a ^ 2 * (x ^ 2 + y ^ 2) + b ^ 2 * (x ^ 2 + z ^ 2) +
          c ^ 2 * (y ^ 2 + z ^ 2) -
          2 * (a * b * y * z + a * c * x * z + b * c * x * y) =
        (y * a - z * b) ^ 2 + (x * a - z * c) ^ 2 +
          (x * b - y * c) ^ 2 := by ring
  nlinarith [hid]

theorem fourBridge_triangle_correct_nonneg
    {x y z a b c : Real}
    (hx0 : 0 <= x) (hy0 : 0 <= y) (hz0 : 0 <= z)
    (hx1 : x <= 1) (hy1 : y <= 1) (hz1 : z <= 1)
    (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c)
    (hxa : x * a ^ 2 <= (1 - x ^ 2) * y * a)
    (hya : y * a ^ 2 <= (1 - y ^ 2) * x * a)
    (hxb : x * b ^ 2 <= (1 - x ^ 2) * z * b)
    (hzb : z * b ^ 2 <= (1 - z ^ 2) * x * b)
    (hyc : y * c ^ 2 <= (1 - y ^ 2) * z * c)
    (hzc : z * c ^ 2 <= (1 - z ^ 2) * y * c) :
    0 <=
      x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) +
        z ^ 2 * (1 - z ^ 4) +
      9 * (a * x * y * (x ^ 2 + y ^ 2) +
        b * x * z * (x ^ 2 + z ^ 2) +
        c * y * z * (y ^ 2 + z ^ 2)) +
      9 / 2 * (a ^ 2 * (x ^ 2 + y ^ 2) +
        b ^ 2 * (x ^ 2 + z ^ 2) + c ^ 2 * (y ^ 2 + z ^ 2)) +
      (-18 * a * b * y * z +
        6 * x * a * b * (x * y * z + y * b + z * a)) +
      (-18 * a * c * x * z +
        6 * y * a * c * (x * y * z + x * c + z * a)) +
      (-18 * b * c * x * y +
        6 * z * b * c * (x * y * z + x * c + y * b)) := by
  by_cases hzero : x = 0 ∨ y = 0 ∨ z = 0
  · exact fourBridge_triangle_correct_nonneg_of_any_eq_zero
      hx0 hy0 hz0 hx1 hy1 hz1 ha hb hc
      hxa hya hxb hzb hyc hzc hzero
  · have hx : 0 < x := lt_of_le_of_ne hx0 (by tauto)
    have hy : 0 < y := lt_of_le_of_ne hy0 (by tauto)
    have hz : 0 < z := lt_of_le_of_ne hz0 (by tauto)
    rcases le_total 1 (x ^ 2 + y ^ 2 + z ^ 2) with hhigh | hlow
    · exact fourBridge_triangle_correct_nonneg_of_sqsum_ge_one
        hx0 hy0 hz0 hx1 hy1 hz1 ha hb hc
        hxa hya hxb hzb hyc hzc hhigh
    · exact fourBridge_triangle_correct_nonneg_of_sqsum_le_one
        hx0 hy0 hz0 hx hy hz hx1 hy1 hz1 ha hb hc
        hxa hya hxb hzb hyc hzc hlow

set_option maxHeartbeats 1600000 in
theorem fourBridge_Ursell_correction_nonneg
    {m0 m1 m2 m3 c01 c02 c03 c12 c13 c23 : Real}
    (hm00 : 0 <= m0) (hm10 : 0 <= m1) (hm20 : 0 <= m2) (hm30 : 0 <= m3)
    (hm01 : m0 <= 1) (hm11 : m1 <= 1) (hm21 : m2 <= 1) (hm31 : m3 <= 1)
    (hc01 : 0 <= c01) (hc02 : 0 <= c02) (hc03 : 0 <= c03)
    (hc12 : 0 <= c12) (hc13 : 0 <= c13) (hc23 : 0 <= c23)
    (h001 : m0 * c01 ^ 2 <= (1 - m0 ^ 2) * m1 * c01)
    (h101 : m1 * c01 ^ 2 <= (1 - m1 ^ 2) * m0 * c01)
    (h002 : m0 * c02 ^ 2 <= (1 - m0 ^ 2) * m2 * c02)
    (h202 : m2 * c02 ^ 2 <= (1 - m2 ^ 2) * m0 * c02)
    (h003 : m0 * c03 ^ 2 <= (1 - m0 ^ 2) * m3 * c03)
    (h303 : m3 * c03 ^ 2 <= (1 - m3 ^ 2) * m0 * c03)
    (h112 : m1 * c12 ^ 2 <= (1 - m1 ^ 2) * m2 * c12)
    (h212 : m2 * c12 ^ 2 <= (1 - m2 ^ 2) * m1 * c12)
    (h113 : m1 * c13 ^ 2 <= (1 - m1 ^ 2) * m3 * c13)
    (h313 : m3 * c13 ^ 2 <= (1 - m3 ^ 2) * m1 * c13)
    (h223 : m2 * c23 ^ 2 <= (1 - m2 ^ 2) * m3 * c23)
    (h323 : m3 * c23 ^ 2 <= (1 - m3 ^ 2) * m2 * c23) :
    let p01 := m0 * m1 + c01
    let p02 := m0 * m2 + c02
    let p03 := m0 * m3 + c03
    let p12 := m1 * m2 + c12
    let p13 := m1 * m3 + c13
    let p23 := m2 * m3 + c23
    let u012 := m0 * p12 + m1 * p02 + m2 * p01 - 2 * m0 * m1 * m2
    let u013 := m0 * p13 + m1 * p03 + m3 * p01 - 2 * m0 * m1 * m3
    let u023 := m0 * p23 + m2 * p03 + m3 * p02 - 2 * m0 * m2 * m3
    let u123 := m1 * p23 + m2 * p13 + m3 * p12 - 2 * m1 * m2 * m3
    let aa := m0 ^ 2 + m1 ^ 2 + m2 ^ 2 + m3 ^ 2
    let bb := p01 ^ 2 + p02 ^ 2 + p03 ^ 2 +
      p12 ^ 2 + p13 ^ 2 + p23 ^ 2
    0 <= aa + 3 * aa * bb - aa ^ 3 -
        3 * (u012 ^ 2 + u013 ^ 2 + u023 ^ 2 + u123 ^ 2) +
      2 * (m0 * c01 * c02 *
          (m0 * m1 * m2 + m1 * c02 + m2 * c01) +
        m1 * c01 * c12 *
          (m0 * m1 * m2 + m0 * c12 + m2 * c01) +
        m2 * c02 * c12 *
          (m0 * m1 * m2 + m0 * c12 + m1 * c02)) +
      2 * (m0 * c01 * c03 *
          (m0 * m1 * m3 + m1 * c03 + m3 * c01) +
        m1 * c01 * c13 *
          (m0 * m1 * m3 + m0 * c13 + m3 * c01) +
        m3 * c03 * c13 *
          (m0 * m1 * m3 + m0 * c13 + m1 * c03)) +
      2 * (m0 * c02 * c03 *
          (m0 * m2 * m3 + m2 * c03 + m3 * c02) +
        m2 * c02 * c23 *
          (m0 * m2 * m3 + m0 * c23 + m3 * c02) +
        m3 * c03 * c23 *
          (m0 * m2 * m3 + m0 * c23 + m2 * c03)) +
      2 * (m1 * c12 * c13 *
          (m1 * m2 * m3 + m2 * c13 + m3 * c12) +
        m2 * c12 * c23 *
          (m1 * m2 * m3 + m1 * c23 + m3 * c12) +
        m3 * c13 * c23 *
          (m1 * m2 * m3 + m1 * c23 + m2 * c13)) := by
  have h012 := fourBridge_triangle_correct_nonneg
    hm00 hm10 hm20 hm01 hm11 hm21 hc01 hc02 hc12
    h001 h101 h002 h202 h112 h212
  have h013 := fourBridge_triangle_correct_nonneg
    hm00 hm10 hm30 hm01 hm11 hm31 hc01 hc03 hc13
    h001 h101 h003 h303 h113 h313
  have h023 := fourBridge_triangle_correct_nonneg
    hm00 hm20 hm30 hm01 hm21 hm31 hc02 hc03 hc23
    h002 h202 h003 h303 h223 h323
  have h123 := fourBridge_triangle_correct_nonneg
    hm10 hm20 hm30 hm11 hm21 hm31 hc12 hc13 hc23
    h112 h212 h113 h313 h223 h323
  have hbase := fourBridge_zero_base_identity
    m0 m1 m2 m3 c01 c02 c03 c12 c13 c23
  dsimp at hbase ⊢
  rw [hbase]
  nlinarith

set_option maxHeartbeats 6000000 in
theorem fourBridgeVarianceSkewBernsteinCoeff_zero_nonpos
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : Sym2 V -> Real) (hf : V -> Real)
    (hK : forall e, 0 <= K e) (hhf : forall v, 0 <= hf v)
    {w x y z : V}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    fourBridgeVarianceSkewBernsteinCoeff
        (fourBridgeOneCoeff G K hf w x y z)
        (fourBridgeTwoCoeff G K hf w x y z)
        (fourBridgeThreeCoeff G K hf w x y z)
        (fourBridgeFourCoeff G K hf w x y z) 0 <= 0 := by
  let m0 := grahamInhomOne G K hf w
  let m1 := grahamInhomOne G K hf x
  let m2 := grahamInhomOne G K hf y
  let m3 := grahamInhomOne G K hf z
  let c01 := ghsiCovariance G K hf w x
  let c02 := ghsiCovariance G K hf w y
  let c03 := ghsiCovariance G K hf w z
  let c12 := ghsiCovariance G K hf x y
  let c13 := ghsiCovariance G K hf x z
  let c23 := ghsiCovariance G K hf y z
  have hm00 := grahamInhomOne_nonneg G K hf hK hhf w
  have hm10 := grahamInhomOne_nonneg G K hf hK hhf x
  have hm20 := grahamInhomOne_nonneg G K hf hK hhf y
  have hm30 := grahamInhomOne_nonneg G K hf hK hhf z
  have hm01 := grahamInhomOne_le_one G K hf w
  have hm11 := grahamInhomOne_le_one G K hf x
  have hm21 := grahamInhomOne_le_one G K hf y
  have hm31 := grahamInhomOne_le_one G K hf z
  have hc01 := grahamInhomCov_nonneg G K hf hK hhf w x
  have hc02 := grahamInhomCov_nonneg G K hf hK hhf w y
  have hc03 := grahamInhomCov_nonneg G K hf hK hhf w z
  have hc12 := grahamInhomCov_nonneg G K hf hK hhf x y
  have hc13 := grahamInhomCov_nonneg G K hf hK hhf x z
  have hc23 := grahamInhomCov_nonneg G K hf hK hhf y z
  have h001 := grahamInhom_pair_covariance_square_le G K hf hK hhf w x
  have h101 := grahamInhom_pair_covariance_square_le G K hf hK hhf x w
  have h002 := grahamInhom_pair_covariance_square_le G K hf hK hhf w y
  have h202 := grahamInhom_pair_covariance_square_le G K hf hK hhf y w
  have h003 := grahamInhom_pair_covariance_square_le G K hf hK hhf w z
  have h303 := grahamInhom_pair_covariance_square_le G K hf hK hhf z w
  have h112 := grahamInhom_pair_covariance_square_le G K hf hK hhf x y
  have h212 := grahamInhom_pair_covariance_square_le G K hf hK hhf y x
  have h113 := grahamInhom_pair_covariance_square_le G K hf hK hhf x z
  have h313 := grahamInhom_pair_covariance_square_le G K hf hK hhf z x
  have h223 := grahamInhom_pair_covariance_square_le G K hf hK hhf y z
  have h323 := grahamInhom_pair_covariance_square_le G K hf hK hhf z y
  rw [ghsiCovariance_comm G K hf x w] at h101
  rw [ghsiCovariance_comm G K hf y w] at h202
  rw [ghsiCovariance_comm G K hf z w] at h303
  rw [ghsiCovariance_comm G K hf y x] at h212
  rw [ghsiCovariance_comm G K hf z x] at h313
  rw [ghsiCovariance_comm G K hf z y] at h323
  have hscalar := fourBridge_Ursell_correction_nonneg
    (m0 := m0) (m1 := m1) (m2 := m2) (m3 := m3)
    (c01 := c01) (c02 := c02) (c03 := c03)
    (c12 := c12) (c13 := c13) (c23 := c23)
    hm00 hm10 hm20 hm30 hm01 hm11 hm21 hm31
    hc01 hc02 hc03 hc12 hc13 hc23
    h001 h101 h002 h202 h003 h303 h112 h212 h113 h313 h223 h323
  have hcorr012 := grahamInhomThreePoint_square_correction_le
    G K hf hK hhf hwx hwy hxy
  have hcorr013 := grahamInhomThreePoint_square_correction_le
    G K hf hK hhf hwx hwz hxz
  have hcorr023 := grahamInhomThreePoint_square_correction_le
    G K hf hK hhf hwy hwz hyz
  have hcorr123 := grahamInhomThreePoint_square_correction_le
    G K hf hK hhf hxy hxz hyz
  have hp01 : expJ G.edgeFinset K hf (fun s => spin s w * spin s x) =
      m0 * m1 + c01 := by
    dsimp [m0, m1, c01]
    unfold grahamInhomOne ghsiCovariance
    ring
  have hp02 : expJ G.edgeFinset K hf (fun s => spin s w * spin s y) =
      m0 * m2 + c02 := by
    dsimp [m0, m2, c02]
    unfold grahamInhomOne ghsiCovariance
    ring
  have hp03 : expJ G.edgeFinset K hf (fun s => spin s w * spin s z) =
      m0 * m3 + c03 := by
    dsimp [m0, m3, c03]
    unfold grahamInhomOne ghsiCovariance
    ring
  have hp12 : expJ G.edgeFinset K hf (fun s => spin s x * spin s y) =
      m1 * m2 + c12 := by
    dsimp [m1, m2, c12]
    unfold grahamInhomOne ghsiCovariance
    ring
  have hp13 : expJ G.edgeFinset K hf (fun s => spin s x * spin s z) =
      m1 * m3 + c13 := by
    dsimp [m1, m3, c13]
    unfold grahamInhomOne ghsiCovariance
    ring
  have hp23 : expJ G.edgeFinset K hf (fun s => spin s y * spin s z) =
      m2 * m3 + c23 := by
    dsimp [m2, m3, c23]
    unfold grahamInhomOne ghsiCovariance
    ring
  have hone : fourBridgeOneCoeff G K hf w x y z =
      m0 ^ 2 + m1 ^ 2 + m2 ^ 2 + m3 ^ 2 := by
    unfold fourBridgeOneCoeff
    dsimp [m0, m1, m2, m3, grahamInhomOne]
  have htwo : fourBridgeTwoCoeff G K hf w x y z =
      (m0 * m1 + c01) ^ 2 + (m0 * m2 + c02) ^ 2 +
        (m0 * m3 + c03) ^ 2 + (m1 * m2 + c12) ^ 2 +
        (m1 * m3 + c13) ^ 2 + (m2 * m3 + c23) ^ 2 := by
    unfold fourBridgeTwoCoeff
    rw [hp01, hp02, hp03, hp12, hp13, hp23]
  have hthree : fourBridgeThreeCoeff G K hf w x y z =
      (expJ G.edgeFinset K hf
          (fun s => spin s w * (spin s x * spin s y))) ^ 2 +
        (expJ G.edgeFinset K hf
          (fun s => spin s w * (spin s x * spin s z))) ^ 2 +
        (expJ G.edgeFinset K hf
          (fun s => spin s w * (spin s y * spin s z))) ^ 2 +
        (expJ G.edgeFinset K hf
          (fun s => spin s x * (spin s y * spin s z))) ^ 2 := by
    rfl
  dsimp at hscalar hcorr012 hcorr013 hcorr023 hcorr123
  simp only [fourBridgeVarianceSkewBernsteinCoeff]
  rw [hone, htwo, hthree]
  dsimp [m0, m1, m2, m3, c01, c02, c03, c12, c13, c23]
  clear hm00 hm10 hm20 hm30 hm01 hm11 hm21 hm31
  clear hc01 hc02 hc03 hc12 hc13 hc23
  clear h001 h101 h002 h202 h003 h303 h112 h212 h113 h313 h223 h323
  clear hp01 hp02 hp03 hp12 hp13 hp23 hone htwo hthree
  linarith [hscalar, hcorr012, hcorr013, hcorr023, hcorr123]

end LowFaceCertificate
end
end StatMech.Ising
