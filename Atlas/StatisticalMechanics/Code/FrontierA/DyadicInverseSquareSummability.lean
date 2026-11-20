/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real









open Filter Finset Set Topology

namespace StatMech.FrontierA

noncomputable section

private theorem exists_le_two_pow (x : Real) :
    ∃ n : Nat, x ≤ (2 : Real) ^ n := by
  have h := (tendsto_pow_atTop_atTop_of_one_lt
    (r := (2 : Real)) (by norm_num)).eventually (eventually_ge_atTop x)
  exact h.exists


noncomputable def dyadicUpperLevel {Q : Type*} (size : Q → Real) (q : Q) : Nat :=
  Nat.find (exists_le_two_pow (size q))

theorem size_le_two_pow_dyadicUpperLevel
    {Q : Type*} (size : Q → Real) (q : Q) :
    size q ≤ (2 : Real) ^ dyadicUpperLevel size q :=
  Nat.find_spec (exists_le_two_pow (size q))

theorem two_pow_lt_size_of_lt_dyadicUpperLevel
    {Q : Type*} (size : Q → Real) (q : Q) {n : Nat}
    (hn : n < dyadicUpperLevel size q) :
    (2 : Real) ^ n < size q := by
  by_contra h
  have hle : size q ≤ (2 : Real) ^ n := le_of_not_gt h
  have := Nat.find_min' (exists_le_two_pow (size q)) hle
  exact (Nat.not_le_of_lt hn) this


def DyadicUpperFiber {Q : Type*} (size : Q → Real) (n : Nat) :=
  {q : Q // dyadicUpperLevel size q = n}

private theorem finite_dyadicUpperFiber
    {Q : Type*} (size : Q → Real)
    (hfinite : ∀ R : Real, Set.Finite {q | size q ≤ R}) (n : Nat) :
    Finite (DyadicUpperFiber size n) := by
  let target : Set Q := {q | size q ≤ (2 : Real) ^ n}
  have htarget : target.Finite := hfinite ((2 : Real) ^ n)
  letI : Fintype target := htarget.fintype
  let f : DyadicUpperFiber size n → target := fun q =>
    ⟨q.1, by
      change size q.1 ≤ (2 : Real) ^ n
      simpa [q.2] using size_le_two_pow_dyadicUpperLevel size q.1⟩
  exact Finite.of_injective f (by
    intro a b h
    apply Subtype.ext
    change a.1 = b.1
    exact congrArg (fun x : target => x.1) h)

private def dyadicUpperEquiv {Q : Type*} (size : Q → Real) :
    (Σ n : Nat, DyadicUpperFiber size n) ≃ Q where
  toFun q := q.2.1
  invFun q := ⟨dyadicUpperLevel size q, ⟨q, rfl⟩⟩
  left_inv q := by
    rcases q with ⟨n, q, hq⟩
    cases hq
    rfl
  right_inv q := rfl

private theorem inverse_sq_le_dyadic_majorant
    {Q : Type*} {size : Q → Real}
    (hsize : ∀ q, 1 ≤ size q) (q : Q) :
    1 / size q ^ 2 ≤
      4 * (1 / 4 : Real) ^ dyadicUpperLevel size q := by
  let n := dyadicUpperLevel size q
  have hlower : (2 : Real) ^ n / 2 ≤ size q := by
    by_cases hn : n = 0
    · rw [hn]
      norm_num
      linarith [hsize q]
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn
      have hlt : (2 : Real) ^ m < size q :=
        two_pow_lt_size_of_lt_dyadicUpperLevel size q (by
          change m < dyadicUpperLevel size q
          rw [show dyadicUpperLevel size q = m + 1 by exact hm]
          omega)
      rw [hm]
      simpa [pow_succ] using hlt.le
  have hbase : 0 < (2 : Real) ^ n / 2 := by positivity
  have hsquare : ((2 : Real) ^ n / 2) ^ 2 ≤ size q ^ 2 :=
    (sq_le_sq₀ hbase.le (le_trans hbase.le hlower)).2 hlower
  calc
    1 / size q ^ 2 ≤ 1 / (((2 : Real) ^ n / 2) ^ 2) :=
      one_div_le_one_div_of_le (sq_pos_of_pos hbase) hsquare
    _ = 4 * (1 / 4 : Real) ^ n := by
      rw [div_pow]
      norm_num [div_eq_mul_inv, mul_pow]
      rw [show ((2 : Real) ^ n) ^ 2 = (4 : Real) ^ n by
        simp only [pow_two]
        rw [← mul_pow]
        norm_num]
      rw [← inv_pow]
      norm_num


theorem summable_inverse_sq_of_linear_sublevel_count
    {Q : Type*} [Countable Q] (size : Q → Real)
    (hsize : ∀ q, 1 ≤ size q)
    (hfinite : ∀ R : Real, Set.Finite {q | size q ≤ R})
    {A B : Real} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcount : ∀ R : Real, 1 ≤ R →
      (Nat.card {q : Q // size q ≤ R} : Real) ≤ A + B * R) :
    Summable (fun q : Q => 1 / size q ^ 2) := by
  classical
  let major : Nat → Real := fun n =>
    4 * A * (1 / 4 : Real) ^ n + 4 * B * (1 / 2 : Real) ^ n
  have hmajor : Summable major := by
    apply Summable.add
    · exact (summable_geometric_of_lt_one (by norm_num : (0 : Real) ≤ 1 / 4)
        (by norm_num : (1 : Real) / 4 < 1)).mul_left (4 * A)
    · exact (summable_geometric_of_lt_one (by norm_num : (0 : Real) ≤ 1 / 2)
        (by norm_num : (1 : Real) / 2 < 1)).mul_left (4 * B)
  have hfiberSummable : ∀ n : Nat,
      Summable (fun q : DyadicUpperFiber size n => 1 / size q.1 ^ 2) := by
    intro n
    letI : Finite (DyadicUpperFiber size n) :=
      finite_dyadicUpperFiber size hfinite n
    letI : Fintype (DyadicUpperFiber size n) := Fintype.ofFinite _
    exact (hasSum_fintype (fun q : DyadicUpperFiber size n =>
      1 / size q.1 ^ 2)).summable
  have hfiberBound : ∀ n : Nat,
      ∑' q : DyadicUpperFiber size n, 1 / size q.1 ^ 2 ≤ major n := by
    intro n
    letI : Finite (DyadicUpperFiber size n) :=
      finite_dyadicUpperFiber size hfinite n
    letI : Fintype (DyadicUpperFiber size n) := Fintype.ofFinite _
    rw [tsum_fintype]
    have hterm : ∀ q : DyadicUpperFiber size n,
        1 / size q.1 ^ 2 ≤ 4 * (1 / 4 : Real) ^ n := by
      intro q
      simpa [q.2] using inverse_sq_le_dyadic_majorant hsize q.1
    calc
      (∑ q : DyadicUpperFiber size n, 1 / size q.1 ^ 2) ≤
          (Fintype.card (DyadicUpperFiber size n) : Real) *
            (4 * (1 / 4 : Real) ^ n) := by
        simpa [nsmul_eq_mul] using
          Finset.sum_le_card_nsmul Finset.univ
            (fun q : DyadicUpperFiber size n => 1 / size q.1 ^ 2)
            (4 * (1 / 4 : Real) ^ n)
            (fun q _ => hterm q)
      _ ≤ (A + B * (2 : Real) ^ n) *
            (4 * (1 / 4 : Real) ^ n) := by
        gcongr
        have hsub : Nat.card (DyadicUpperFiber size n) ≤
            Nat.card {q : Q // size q ≤ (2 : Real) ^ n} := by
          letI : Fintype {q : Q // size q ≤ (2 : Real) ^ n} :=
            (hfinite ((2 : Real) ^ n)).fintype
          let f : DyadicUpperFiber size n →
              {q : Q // size q ≤ (2 : Real) ^ n} := fun q =>
            ⟨q.1, by simpa [q.2] using
              size_le_two_pow_dyadicUpperLevel size q.1⟩
          exact Nat.card_le_card_of_injective f
            (by
              intro a b h
              apply Subtype.ext
              change a.1 = b.1
              exact congrArg (fun x :
                {q : Q // size q ≤ (2 : Real) ^ n} => x.1) h)
        have hsubR : (Nat.card (DyadicUpperFiber size n) : Real) ≤
            (Nat.card {q : Q // size q ≤ (2 : Real) ^ n} : Real) := by
          exact_mod_cast hsub
        rw [← Nat.card_eq_fintype_card]
        exact hsubR.trans
          (hcount ((2 : Real) ^ n) (one_le_pow₀ (by norm_num)))
      _ = major n := by
        dsimp [major]
        have hp : (2 : Real) ^ n * (1 / 4 : Real) ^ n =
            (1 / 2 : Real) ^ n := by
          rw [← mul_pow]
          norm_num
        calc
          (A + B * (2 : Real) ^ n) * (4 * (1 / 4 : Real) ^ n) =
              4 * A * (1 / 4 : Real) ^ n +
                4 * B * ((2 : Real) ^ n * (1 / 4 : Real) ^ n) := by ring
          _ = 4 * A * (1 / 4 : Real) ^ n +
                4 * B * (1 / 2 : Real) ^ n := by rw [hp]
  have houter : Summable (fun n : Nat =>
      ∑' q : DyadicUpperFiber size n, 1 / size q.1 ^ 2) := by
    exact Summable.of_nonneg_of_le
      (fun n => tsum_nonneg fun q => by positivity)
      hfiberBound hmajor
  have hsigma : Summable (fun q : Σ n : Nat, DyadicUpperFiber size n =>
      1 / size q.2.1 ^ 2) :=
    (summable_sigma_of_nonneg (fun q => by positivity)).2
      ⟨hfiberSummable, houter⟩
  exact ((dyadicUpperEquiv size).summable_iff).1 (by simpa using hsigma)


theorem tsum_inverse_sq_le_of_linear_sublevel_count
    {Q : Type*} [Countable Q] (size : Q -> Real)
    (hsize : forall q, 1 <= size q)
    (hfinite : forall R : Real, Set.Finite {q | size q <= R})
    {A B : Real} (hA : 0 <= A) (hB : 0 <= B)
    (hcount : forall R : Real, 1 <= R ->
      (Nat.card {q : Q // size q <= R} : Real) <= A + B * R) :
    ∑' q : Q, 1 / size q ^ 2 <= (16 / 3 : Real) * A + 8 * B := by
  classical
  let major : Nat -> Real := fun n =>
    4 * A * (1 / 4 : Real) ^ n + 4 * B * (1 / 2 : Real) ^ n
  have hmajor : Summable major := by
    apply Summable.add
    · exact (summable_geometric_of_lt_one (by norm_num : (0 : Real) <= 1 / 4)
        (by norm_num : (1 : Real) / 4 < 1)).mul_left (4 * A)
    · exact (summable_geometric_of_lt_one (by norm_num : (0 : Real) <= 1 / 2)
        (by norm_num : (1 : Real) / 2 < 1)).mul_left (4 * B)
  have hfiberSummable : forall n : Nat,
      Summable (fun q : DyadicUpperFiber size n => 1 / size q.1 ^ 2) := by
    intro n
    letI : Finite (DyadicUpperFiber size n) :=
      finite_dyadicUpperFiber size hfinite n
    exact summable_of_finite_support (Set.finite_univ.subset (Set.subset_univ _))
  have hfiberBound : forall n : Nat,
      ∑' q : DyadicUpperFiber size n, 1 / size q.1 ^ 2 <= major n := by
    intro n
    letI : Finite (DyadicUpperFiber size n) :=
      finite_dyadicUpperFiber size hfinite n
    letI : Fintype (DyadicUpperFiber size n) := Fintype.ofFinite _
    rw [tsum_fintype]
    have hterm : forall q : DyadicUpperFiber size n,
        1 / size q.1 ^ 2 <= 4 * (1 / 4 : Real) ^ n := by
      intro q
      simpa [q.2] using inverse_sq_le_dyadic_majorant hsize q.1
    calc
      (∑ q : DyadicUpperFiber size n, 1 / size q.1 ^ 2) <=
          (Fintype.card (DyadicUpperFiber size n) : Real) *
            (4 * (1 / 4 : Real) ^ n) := by
        simpa [nsmul_eq_mul] using
          Finset.sum_le_card_nsmul Finset.univ
            (fun q : DyadicUpperFiber size n => 1 / size q.1 ^ 2)
            (4 * (1 / 4 : Real) ^ n) (fun q _ => hterm q)
      _ <= (A + B * (2 : Real) ^ n) *
            (4 * (1 / 4 : Real) ^ n) := by
        gcongr
        have hsub : Nat.card (DyadicUpperFiber size n) <=
            Nat.card {q : Q // size q <= (2 : Real) ^ n} := by
          letI : Fintype {q : Q // size q <= (2 : Real) ^ n} :=
            (hfinite ((2 : Real) ^ n)).fintype
          let f : DyadicUpperFiber size n ->
              {q : Q // size q <= (2 : Real) ^ n} := fun q =>
            ⟨q.1, by simpa [q.2] using
              size_le_two_pow_dyadicUpperLevel size q.1⟩
          exact Nat.card_le_card_of_injective f (by
            intro a b hab
            apply Subtype.ext
            exact congrArg (fun x : {q : Q // size q <= (2 : Real) ^ n} => x.1) hab)
        have hsubR : (Nat.card (DyadicUpperFiber size n) : Real) <=
            (Nat.card {q : Q // size q <= (2 : Real) ^ n} : Real) := by
          exact_mod_cast hsub
        rw [<- Nat.card_eq_fintype_card]
        exact hsubR.trans
          (hcount ((2 : Real) ^ n) (one_le_pow₀ (by norm_num)))
      _ = major n := by
        dsimp [major]
        have hp : (2 : Real) ^ n * (1 / 4 : Real) ^ n =
            (1 / 2 : Real) ^ n := by
          rw [<- mul_pow]
          norm_num
        rw [show (A + B * (2 : Real) ^ n) * (4 * (1 / 4 : Real) ^ n) =
            4 * A * (1 / 4 : Real) ^ n +
              4 * B * ((2 : Real) ^ n * (1 / 4 : Real) ^ n) by ring, hp]
  have houter : Summable (fun n : Nat =>
      ∑' q : DyadicUpperFiber size n, 1 / size q.1 ^ 2) :=
    Summable.of_nonneg_of_le
      (fun n => tsum_nonneg fun q => by positivity)
      hfiberBound hmajor
  have hsigma : Summable (fun q : Sigma (DyadicUpperFiber size) =>
      1 / size q.2.1 ^ 2) :=
    (summable_sigma_of_nonneg (fun q => by positivity)).2
      ⟨hfiberSummable, houter⟩
  calc
    ∑' q : Q, 1 / size q ^ 2 =
        ∑' q : Sigma (DyadicUpperFiber size), 1 / size q.2.1 ^ 2 := by
      calc
        ∑' q : Q, 1 / size q ^ 2 =
            ∑' q : Sigma (DyadicUpperFiber size),
              1 / size ((dyadicUpperEquiv size) q) ^ 2 :=
          ((dyadicUpperEquiv size).tsum_eq
            (fun q : Q => 1 / size q ^ 2)).symm
        _ = ∑' q : Sigma (DyadicUpperFiber size),
              1 / size q.2.1 ^ 2 := by
          apply tsum_congr
          rintro ⟨n, q⟩
          rfl
    _ = ∑' n : Nat, ∑' q : DyadicUpperFiber size n,
          1 / size q.1 ^ 2 := hsigma.tsum_sigma
    _ <= ∑' n : Nat, major n := houter.tsum_le_tsum hfiberBound hmajor
    _ = (16 / 3 : Real) * A + 8 * B := by
      dsimp [major]
      let hs1 := summable_geometric_of_lt_one
        (by norm_num : (0 : Real) <= 1 / 4)
        (by norm_num : (1 : Real) / 4 < 1)
      let hs2 := summable_geometric_of_lt_one
        (by norm_num : (0 : Real) <= 1 / 2)
        (by norm_num : (1 : Real) / 2 < 1)
      rw [(hs1.mul_left (4 * A)).tsum_add (hs2.mul_left (4 * B)),
        tsum_mul_left, tsum_mul_left]
      rw [(hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : Real)‖ < 1)).tsum_eq,
        (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : Real)‖ < 1)).tsum_eq]
      norm_num
      ring


theorem tsum_inverse_sq_tail_le_of_linear_sublevel_count
    {Q : Type*} [Countable Q] (size : Q -> Real)
    (hfinite : forall S : Real, Set.Finite {q | size q <= S})
    {A B : Real} (hA : 0 <= A) (hB : 0 <= B)
    (hcount : forall S : Real, 1 <= S ->
      (Nat.card {q : Q // size q <= S} : Real) <= A + B * S)
    (R : Real) (hR : 1 <= R) :
    ∑' q : {q : Q // R < size q}, 1 / size q.1 ^ 2 <=
      (16 / 3 : Real) * A / R ^ 2 + 8 * B / R := by
  classical
  let QR := {q : Q // R < size q}
  let scaled : QR -> Real := fun q => size q.1 / R
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hscaledOne : forall q : QR, 1 <= scaled q := by
    intro q
    apply (le_div_iff₀ hRpos).2
    simpa only [one_mul] using q.2.le
  have hscaledFinite : forall S : Real,
      Set.Finite {q : QR | scaled q <= S} := by
    intro S
    let target : Set Q := {q | size q <= R * S}
    have hpre : Set.Finite
        ((fun q : QR => q.1) ⁻¹' {q : Q | size q <= R * S}) :=
      (hfinite (R * S)).preimage Subtype.val_injective.injOn
    apply hpre.subset
    intro q hq
    change size q.1 / R <= S at hq
    change size q.1 <= R * S
    simpa [mul_comm] using (div_le_iff₀ hRpos).1 hq
  have hscaledCount : forall S : Real, 1 <= S ->
      (Nat.card {q : QR // scaled q <= S} : Real) <=
        A + (B * R) * S := by
    intro S hS
    let source := {q : QR // scaled q <= S}
    let target := {q : Q // size q <= R * S}
    letI : Finite source := (hscaledFinite S).to_subtype
    letI : Finite target := (hfinite (R * S)).to_subtype
    let embed : source -> target := fun q => ⟨q.1.1, by
      have hdiv := q.2
      dsimp [scaled] at hdiv
      simpa [mul_comm] using (div_le_iff₀ hRpos).1 hdiv⟩
    have hinj : Function.Injective embed := by
      intro q r hqr
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : target => x.1) hqr
    have hcard := Nat.card_le_card_of_injective embed hinj
    have hcardReal : (Nat.card source : Real) <= (Nat.card target : Real) := by
      exact_mod_cast hcard
    calc
      (Nat.card source : Real) <= (Nat.card target : Real) := hcardReal
      _ <= A + B * (R * S) := hcount (R * S) (by nlinarith)
      _ = A + (B * R) * S := by ring
  have hscaled := tsum_inverse_sq_le_of_linear_sublevel_count scaled
    hscaledOne hscaledFinite hA (mul_nonneg hB hRpos.le) hscaledCount
  have hscaleEq :
      (∑' q : QR, 1 / scaled q ^ 2) =
        R ^ 2 * ∑' q : QR, 1 / size q.1 ^ 2 := by
    rw [<- tsum_mul_left]
    apply tsum_congr
    intro q
    dsimp [scaled]
    field_simp
  rw [hscaleEq] at hscaled
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hRpos
  calc
    ∑' q : QR, 1 / size q.1 ^ 2 =
        (R ^ 2 * ∑' q : QR, 1 / size q.1 ^ 2) / R ^ 2 := by
          field_simp
    _ <= ((16 / 3 : Real) * A + 8 * (B * R)) / R ^ 2 := by
      exact div_le_div_of_nonneg_right hscaled hR2.le
    _ = (16 / 3 : Real) * A / R ^ 2 + 8 * B / R := by
      field_simp



theorem tsum_two_mul_radius_div_sq_add_sq_le_of_linear_sublevel_count
    {Q : Type*} [Countable Q] (size : Q -> Real)
    (hsize : forall q, 1 <= size q)
    (hfinite : forall S : Real, Set.Finite {q | size q <= S})
    {A B : Real} (hA : 0 <= A) (hB : 0 <= B)
    (hcount : forall S : Real, 1 <= S ->
      (Nat.card {q : Q // size q <= S} : Real) <= A + B * S)
    (R : Real) (hR : 1 <= R) :
    ∑' q : Q, 2 * R / (size q ^ 2 + R ^ 2) <= 13 * A + 18 * B := by
  classical
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  let f : Q -> Real := fun q => 2 * R / (size q ^ 2 + R ^ 2)
  have hinv : Summable (fun q : Q => 1 / size q ^ 2) :=
    summable_inverse_sq_of_linear_sublevel_count size hsize hfinite hA hB hcount
  have hf : Summable f := by
    apply Summable.of_nonneg_of_le
      (fun q => div_nonneg (mul_nonneg (by norm_num) hRpos.le)
        (add_nonneg (sq_nonneg _) (sq_nonneg _)))
      (fun q => ?_) (hinv.mul_left (2 * R))
    dsimp [f]
    have hspos : 0 < size q ^ 2 := sq_pos_of_pos (zero_lt_one.trans_le (hsize q))
    calc
      2 * R / (size q ^ 2 + R ^ 2) <= 2 * R / size q ^ 2 := by
        exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hRpos.le)
          hspos (le_add_of_nonneg_right (sq_nonneg R))
      _ = 2 * R * (1 / size q ^ 2) := by ring
  let near : Set Q := {q | size q <= R}
  let far : Set Q := {q | R < size q}
  have hfar : Set.compl near = far := by
    ext q
    change (¬size q ≤ R) ↔ R < size q
    exact not_le
  have hnearFinite : near.Finite := hfinite R
  letI : Finite near := hnearFinite.to_subtype
  letI : Fintype near := Fintype.ofFinite _
  have hsplit := hf.tsum_subtype_add_tsum_subtype_compl near
  have hsplit' : (∑' q : near, f q.1) + (∑' q : far, f q.1) =
      ∑' q : Q, f q := by
    rw [<- hfar]
    exact hsplit
  have hnear : (∑' q : near, f q.1) <= (A + B * R) * (2 / R) := by
    rw [tsum_fintype]
    calc
      (∑ q : near, f q.1) <= (Fintype.card near : Real) * (2 / R) := by
        simpa [nsmul_eq_mul] using
          Finset.sum_le_card_nsmul Finset.univ (fun q : near => f q.1)
            (2 / R) (fun q _ => by
              dsimp [f]
              have hden : R ^ 2 <= size q.1 ^ 2 + R ^ 2 :=
                le_add_of_nonneg_left (sq_nonneg _)
              calc
                2 * R / (size q.1 ^ 2 + R ^ 2) <= 2 * R / R ^ 2 := by
                  exact div_le_div_of_nonneg_left
                    (mul_nonneg (by norm_num) hRpos.le)
                    (sq_pos_of_pos hRpos) hden
                _ = 2 / R := by field_simp)
      _ <= (A + B * R) * (2 / R) := by
        gcongr
        rw [<- Nat.card_eq_fintype_card]
        exact hcount R hR
  have htailInv := tsum_inverse_sq_tail_le_of_linear_sublevel_count
    size hfinite hA hB hcount R hR
  have htail : (∑' q : far, f q.1) <=
      2 * R * ((16 / 3 : Real) * A / R ^ 2 + 8 * B / R) := by
    have hpoint : forall q : far,
        f q.1 <= 2 * R * (1 / size q.1 ^ 2) := by
      intro q
      dsimp [f]
      have hspos : 0 < size q.1 ^ 2 := sq_pos_of_pos
        (zero_lt_one.trans_le (hsize q.1))
      calc
        2 * R / (size q.1 ^ 2 + R ^ 2) <= 2 * R / size q.1 ^ 2 := by
          exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hRpos.le)
            hspos (le_add_of_nonneg_right (sq_nonneg R))
        _ = 2 * R * (1 / size q.1 ^ 2) := by ring
    have htailSummable : Summable (fun q : far =>
        2 * R * (1 / size q.1 ^ 2)) := by
      exact ((summable_subtype_iff_indicator.mpr
        (hinv.indicator far)).mul_left (2 * R))
    calc
      (∑' q : far, f q.1) <=
          ∑' q : far, 2 * R * (1 / size q.1 ^ 2) :=
        (hf.subtype far).tsum_le_tsum hpoint htailSummable
      _ = 2 * R * ∑' q : far, 1 / size q.1 ^ 2 := by
        rw [tsum_mul_left]
      _ <= 2 * R * ((16 / 3 : Real) * A / R ^ 2 + 8 * B / R) := by
        gcongr
        simpa [far] using htailInv
  calc
    ∑' q : Q, 2 * R / (size q ^ 2 + R ^ 2) =
        (∑' q : near, f q.1) + (∑' q : far, f q.1) := by
      dsimp [f] at hsplit ⊢
      exact hsplit'.symm
    _ <= (A + B * R) * (2 / R) +
        2 * R * ((16 / 3 : Real) * A / R ^ 2 + 8 * B / R) :=
      add_le_add hnear htail
    _ <= 13 * A + 18 * B := by
      have hRinv : 1 / R <= 1 := (div_le_one hRpos).2 hR
      field_simp
      nlinarith [mul_nonneg hA (sub_nonneg.mpr hR),
        mul_nonneg hB (sub_nonneg.mpr hR)]

end

end StatMech.FrontierA
