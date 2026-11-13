/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardIncidentStairPatch










namespace StatMech.FrontierA

open scoped NNReal
open Set


structure KWStairParameterData
    {n S : ℕ} [NeZero n] [NeZero S]
    (polygon : KWFiniteSimplePolygon n) where
  parameter : Fin n → Fin (S + 1) → ℝ
  parameter_zero : ∀ i, parameter i 0 = 0
  parameter_last : ∀ i, parameter i (Fin.last S) = 1
  parameter_strict : ∀ i (k : Fin S),
    parameter i k.castSucc < parameter i k.succ



noncomputable def kwEndpointParameter (M : ℕ) (beta alpha : ℝ)
    (k : Fin (M + 3)) : ℝ :=
  if k.val = 0 then 0
  else if k.val = M + 2 then 1
  else beta + ((k.val - 1 : ℕ) : ℝ) / M * (1 - alpha - beta)

@[simp] theorem kwEndpointParameter_zero (M : ℕ) (beta alpha : ℝ) :
    kwEndpointParameter M beta alpha 0 = 0 := by
  simp [kwEndpointParameter]

@[simp] theorem kwEndpointParameter_last (M : ℕ) (beta alpha : ℝ) :
    kwEndpointParameter M beta alpha (Fin.last (M + 2)) = 1 := by
  simp [kwEndpointParameter]

theorem kwEndpointParameter_strict
    (M : ℕ) (beta alpha : ℝ)
    (hM : 0 < M) (hbeta : 0 < beta) (halpha : 0 < alpha)
    (hsum : alpha + beta < 1) (k : Fin (M + 2)) :
    kwEndpointParameter M beta alpha k.castSucc <
      kwEndpointParameter M beta alpha k.succ := by
  have hklt := k.isLt
  by_cases hk0 : k.val = 0
  · have hsucc0 : k.val + 1 ≠ 0 := by omega
    have hsuccLast : k.val + 1 ≠ M + 2 := by omega
    simp only [kwEndpointParameter, Fin.val_castSucc, Fin.val_succ,
      if_pos hk0, if_neg hsucc0, if_neg hsuccLast]
    norm_num [hk0]
    exact hbeta
  · by_cases hklast : k.val + 1 = M + 2
    · have hkLast : k.val ≠ M + 2 := by omega
      have hsub : k.val - 1 = M := by omega
      simp only [kwEndpointParameter, Fin.val_castSucc, Fin.val_succ,
        if_neg hk0, if_neg hkLast, if_neg (by omega : k.val + 1 ≠ 0),
        if_pos hklast]
      rw [hsub]
      have hMreal : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
      rw [div_self hMreal, one_mul]
      linarith
    · have hkNotLast : k.val ≠ M + 2 := by omega
      have hsucc0 : k.val + 1 ≠ 0 := by omega
      simp only [kwEndpointParameter, Fin.val_castSucc, Fin.val_succ,
        if_neg hk0, if_neg hkNotLast, if_neg hsucc0, if_neg hklast]
      have hkpos : 1 ≤ k.val := by omega
      have hsubSucc : k.val + 1 - 1 = k.val := by omega
      rw [hsubSucc]
      have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
      have hcentral : 0 < 1 - alpha - beta := by linarith
      have hnum : ((k.val - 1 : ℕ) : ℝ) < (k.val : ℝ) := by
        exact_mod_cast (by omega : k.val - 1 < k.val)
      have hfrac : ((k.val - 1 : ℕ) : ℝ) / M <
          (k.val : ℝ) / M :=
        (div_lt_div_iff_of_pos_right hMreal).mpr hnum
      simpa only [add_comm] using
        (add_lt_add_left (mul_lt_mul_of_pos_right hfrac hcentral) beta)

theorem kwEndpointParameter_step_le_inv
    (M : ℕ) (beta alpha : ℝ)
    (hM : 0 < M) (hbeta : 0 ≤ beta) (halpha : 0 ≤ alpha)
    (hbetaBound : beta ≤ (M : ℝ)⁻¹)
    (halphaBound : alpha ≤ (M : ℝ)⁻¹)
    (k : Fin (M + 2)) :
    kwEndpointParameter M beta alpha k.succ -
        kwEndpointParameter M beta alpha k.castSucc ≤ (M : ℝ)⁻¹ := by
  have hklt := k.isLt
  have hMreal : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  by_cases hk0 : k.val = 0
  · have hsucc0 : k.val + 1 ≠ 0 := by omega
    have hsuccLast : k.val + 1 ≠ M + 2 := by omega
    simp only [kwEndpointParameter, Fin.val_castSucc, Fin.val_succ,
      if_pos hk0, if_neg hsucc0, if_neg hsuccLast]
    norm_num [hk0]
    exact hbetaBound
  · by_cases hklast : k.val + 1 = M + 2
    · have hkLast : k.val ≠ M + 2 := by omega
      have hsub : k.val - 1 = M := by omega
      simp only [kwEndpointParameter, Fin.val_castSucc, Fin.val_succ,
        if_neg hk0, if_neg hkLast, if_neg (by omega : k.val + 1 ≠ 0),
        if_pos hklast]
      rw [hsub, div_self hMreal, one_mul]
      (convert halphaBound using 1; ring)
    · have hkNotLast : k.val ≠ M + 2 := by omega
      have hsucc0 : k.val + 1 ≠ 0 := by omega
      simp only [kwEndpointParameter, Fin.val_castSucc, Fin.val_succ,
        if_neg hk0, if_neg hkNotLast, if_neg hsucc0, if_neg hklast]
      have hsubSucc : k.val + 1 - 1 = k.val := by omega
      rw [hsubSucc]
      have hstep : (((k.val : ℝ) / M) -
          (((k.val - 1 : ℕ) : ℝ) / M)) = (M : ℝ)⁻¹ := by
        have hkpos : 1 ≤ k.val := by omega
        have hcast : ((k.val - 1 : ℕ) : ℝ) = (k.val : ℝ) - 1 := by
          rw [Nat.cast_sub hkpos]
          norm_num
        rw [hcast]
        field_simp
        ring
      have hcentral : 1 - alpha - beta ≤ 1 := by linarith
      have hinv : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
      calc
        beta + (k.val : ℝ) / M * (1 - alpha - beta) -
            (beta + ((k.val - 1 : ℕ) : ℝ) / M *
              (1 - alpha - beta)) =
            ((k.val : ℝ) / M - ((k.val - 1 : ℕ) : ℝ) / M) *
              (1 - alpha - beta) := by ring
        _ = (M : ℝ)⁻¹ * (1 - alpha - beta) := by rw [hstep]
        _ ≤ (M : ℝ)⁻¹ := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hcentral hinv


noncomputable def kwEndpointParameterData
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (M : ℕ) (beta : ℝ) (alpha : Fin n → ℝ)
    (hM : 0 < M) (hbeta : 0 < beta)
    (halpha : ∀ i, 0 < alpha i)
    (hsum : ∀ i, alpha i + beta < 1) :
    KWStairParameterData (S := M + 2) polygon where
  parameter i := kwEndpointParameter M beta (alpha (i + 1))
  parameter_zero i := kwEndpointParameter_zero M beta (alpha (i + 1))
  parameter_last i := kwEndpointParameter_last M beta (alpha (i + 1))
  parameter_strict i k := kwEndpointParameter_strict M beta (alpha (i + 1))
    hM hbeta (halpha (i + 1)) (hsum (i + 1)) k

theorem KWStairParameterData.parameter_strictMono
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon) (i : Fin n) :
    StrictMono (data.parameter i) :=
  Fin.strictMono_iff_lt_succ.mpr (data.parameter_strict i)

def kwStairEvenLocal {S : ℕ} [NeZero S] (k : Fin S) : Fin (2 * S) :=
  ⟨2 * k.val, by have := k.isLt; omega⟩

def kwStairOddLocal {S : ℕ} [NeZero S] (k : Fin S) : Fin (2 * S) :=
  ⟨2 * k.val + 1, by have := k.isLt; omega⟩

def kwStairSliceIndex {S : ℕ} [NeZero S] (l : Fin (2 * S)) : Fin S :=
  ⟨l.val / 2, by
    have hl := l.isLt
    have hS : 0 < S := NeZero.pos S
    omega⟩

theorem kwStairSliceIndex_even {S : ℕ} [NeZero S] (k : Fin S) :
    kwStairSliceIndex (kwStairEvenLocal k) = k := by
  apply Fin.ext
  simp [kwStairSliceIndex, kwStairEvenLocal]

theorem kwStairSliceIndex_odd {S : ℕ} [NeZero S] (k : Fin S) :
    kwStairSliceIndex (kwStairOddLocal k) = k := by
  apply Fin.ext
  simp only [kwStairSliceIndex, kwStairOddLocal]
  omega

@[simp] theorem kwStairEvenLocal_mod_two
    {S : ℕ} [NeZero S] (k : Fin S) :
    (kwStairEvenLocal k).val % 2 = 0 := by
  simp [kwStairEvenLocal]

@[simp] theorem kwStairOddLocal_mod_two
    {S : ℕ} [NeZero S] (k : Fin S) :
    (kwStairOddLocal k).val % 2 = 1 := by
  simp [kwStairOddLocal]

noncomputable def KWStairParameterData.base
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin (S + 1)) : ℂ :=
  AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1))
    (data.parameter i k)

noncomputable def KWStairParameterData.corner
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin S) : ℂ :=
  data.base i k.castSucc +
    (data.parameter i k.succ - data.parameter i k.castSucc) *
      kwHorizontalPart (polygon.edgeVector i)

noncomputable def KWStairParameterData.localVertex
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (l : Fin (2 * S)) : ℂ :=
  if l.val % 2 = 0 then
    data.base i (kwStairSliceIndex l).castSucc
  else
    data.corner i (kwStairSliceIndex l)

@[simp] theorem KWStairParameterData.localVertex_even
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin S) :
    data.localVertex i (kwStairEvenLocal k) = data.base i k.castSucc := by
  simp [KWStairParameterData.localVertex, kwStairSliceIndex_even]

@[simp] theorem KWStairParameterData.localVertex_odd
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin S) :
    data.localVertex i (kwStairOddLocal k) = data.corner i k := by
  simp [KWStairParameterData.localVertex, kwStairSliceIndex_odd]

theorem kwStairLocal_even_or_odd
    {S : ℕ} [NeZero S] (l : Fin (2 * S)) :
    ∃ k : Fin S, l = kwStairEvenLocal k ∨ l = kwStairOddLocal k := by
  let k := kwStairSliceIndex l
  refine ⟨k, ?_⟩
  have hdiv := Nat.mod_add_div l.val 2
  rcases Nat.mod_two_eq_zero_or_one l.val with heven | hodd
  · left
    apply Fin.ext
    dsimp only [k, kwStairSliceIndex, kwStairEvenLocal]
    omega
  · right
    apply Fin.ext
    dsimp only [k, kwStairSliceIndex, kwStairOddLocal]
    omega

theorem KWStairParameterData.base_re
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin (S + 1)) :
    (data.base i k).re = (polygon.vertex i).re +
      data.parameter i k * (polygon.edgeVector i).re := by
  unfold KWStairParameterData.base KWFiniteSimplePolygon.edgeVector
  rw [AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul,
    Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem KWStairParameterData.base_im
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin (S + 1)) :
    (data.base i k).im = (polygon.vertex i).im +
      data.parameter i k * (polygon.edgeVector i).im := by
  unfold KWStairParameterData.base KWFiniteSimplePolygon.edgeVector
  rw [AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul,
    Complex.add_im, Complex.sub_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem KWStairParameterData.corner_re
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin S) :
    (data.corner i k).re = (polygon.vertex i).re +
      data.parameter i k.succ * (polygon.edgeVector i).re := by
  rw [KWStairParameterData.corner, Complex.add_re, data.base_re]
  simp only [kwHorizontalPart, Complex.mul_re, Complex.sub_re,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem KWStairParameterData.corner_im
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin S) :
    (data.corner i k).im = (polygon.vertex i).im +
      data.parameter i k.castSucc * (polygon.edgeVector i).im := by
  rw [KWStairParameterData.corner, Complex.add_im, data.base_im]
  simp only [kwHorizontalPart, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    mul_zero, sub_zero, add_zero]

noncomputable def KWStairParameterData.vertex
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon) :
      Fin (n * (2 * S)) → ℂ :=
  fun j ↦ data.localVertex (finProdFinEquiv.symm j).1
    (finProdFinEquiv.symm j).2

def kwStairEvenIndex
    {n S : ℕ} [NeZero n] [NeZero S]
    (i : Fin n) (k : Fin S) : Fin (n * (2 * S)) :=
  finProdFinEquiv (i, kwStairEvenLocal k)

def kwStairOddIndex
    {n S : ℕ} [NeZero n] [NeZero S]
    (i : Fin n) (k : Fin S) : Fin (n * (2 * S)) :=
  finProdFinEquiv (i, kwStairOddLocal k)

@[simp] theorem KWStairParameterData.vertex_even
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon) (i : Fin n) (k : Fin S) :
    data.vertex (kwStairEvenIndex i k) = data.base i k.castSucc := by
  simp [KWStairParameterData.vertex, kwStairEvenIndex,
    KWStairParameterData.localVertex, kwStairSliceIndex_even]

@[simp] theorem KWStairParameterData.vertex_odd
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon) (i : Fin n) (k : Fin S) :
    data.vertex (kwStairOddIndex i k) = data.corner i k := by
  simp [KWStairParameterData.vertex, kwStairOddIndex,
    KWStairParameterData.localVertex, kwStairSliceIndex_odd]

theorem kwStairEvenIndex_add_one
    {n S : ℕ} [NeZero n] [NeZero S]
    (i : Fin n) (k : Fin S) :
    kwStairEvenIndex i k + 1 = kwStairOddIndex i k := by
  apply Fin.ext
  rw [Fin.val_add]
  have hn : 0 < n := NeZero.pos n
  have hS : 0 < S := NeZero.pos S
  have htotal : 1 < n * (2 * S) := by
    have hnOne : 1 ≤ n := hn
    have htwo : 2 ≤ 2 * S := by omega
    exact lt_of_lt_of_le (by omega : 1 < 1 * 2)
      (Nat.mul_le_mul hnOne htwo)
  have hone : ((1 : Fin (n * (2 * S))).val) = 1 := by
    change 1 % (n * (2 * S)) = 1
    exact Nat.mod_eq_of_lt htotal
  rw [hone]
  simp only [kwStairEvenIndex, kwStairOddIndex, finProdFinEquiv,
    Equiv.coe_fn_mk, kwStairEvenLocal, kwStairOddLocal]
  have hi := i.isLt
  have hk := k.isLt
  have hlocal : 2 * k.val + 1 < 2 * S := by omega
  have hindex : 2 * k.val + 2 * S * i.val + 1 < n * (2 * S) := by
    calc
      2 * k.val + 2 * S * i.val + 1 < 2 * S + 2 * S * i.val := by omega
      _ = (i.val + 1) * (2 * S) := by ring
      _ ≤ n * (2 * S) := Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hi)
  rw [Nat.mod_eq_of_lt hindex]
  omega

theorem kwStairOddIndex_castSucc_add_one
    {n M : ℕ} [NeZero n]
    (i : Fin n) (k : Fin M) :
    kwStairOddIndex (S := M + 1) i k.castSucc + 1 =
      kwStairEvenIndex (S := M + 1) i k.succ := by
  apply Fin.ext
  rw [Fin.val_add]
  have hn : 0 < n := NeZero.pos n
  have htotal : 1 < n * (2 * (M + 1)) := by
    have hnOne : 1 ≤ n := hn
    have htwo : 2 ≤ 2 * (M + 1) := by omega
    exact lt_of_lt_of_le (by omega : 1 < 1 * 2)
      (Nat.mul_le_mul hnOne htwo)
  have hone : ((1 : Fin (n * (2 * (M + 1)))).val) = 1 := by
    change 1 % (n * (2 * (M + 1))) = 1
    exact Nat.mod_eq_of_lt htotal
  rw [hone]
  simp only [kwStairOddIndex, kwStairEvenIndex, finProdFinEquiv,
    Equiv.coe_fn_mk, kwStairOddLocal, kwStairEvenLocal,
    Fin.val_castSucc, Fin.val_succ]
  have hi := i.isLt
  have hk := k.isLt
  have hindex : 2 * k.val + 1 + 2 * (M + 1) * i.val + 1 <
      n * (2 * (M + 1)) := by
    calc
      2 * k.val + 1 + 2 * (M + 1) * i.val + 1 <
          2 * (M + 1) + 2 * (M + 1) * i.val := by omega
      _ = (i.val + 1) * (2 * (M + 1)) := by ring
      _ ≤ n * (2 * (M + 1)) :=
        Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr hi)
  rw [Nat.mod_eq_of_lt hindex]
  omega

theorem kwStairOddIndex_last_add_one
    {n M : ℕ} [NeZero n] (i : Fin n) :
    kwStairOddIndex (S := M + 1) i (Fin.last M) + 1 =
      kwStairEvenIndex (S := M + 1) (i + 1) 0 := by
  apply Fin.ext
  rw [Fin.val_add]
  have hn : 0 < n := NeZero.pos n
  have htotal : 1 < n * (2 * (M + 1)) := by
    have hnOne : 1 ≤ n := hn
    have htwo : 2 ≤ 2 * (M + 1) := by omega
    exact lt_of_lt_of_le (by omega : 1 < 1 * 2)
      (Nat.mul_le_mul hnOne htwo)
  have hone : ((1 : Fin (n * (2 * (M + 1)))).val) = 1 := by
    change 1 % (n * (2 * (M + 1))) = 1
    exact Nat.mod_eq_of_lt htotal
  rw [hone]
  simp only [kwStairOddIndex, kwStairEvenIndex, finProdFinEquiv,
    Equiv.coe_fn_mk, kwStairOddLocal, kwStairEvenLocal,
    Fin.val_last, Fin.val_zero]
  have hi := i.isLt
  by_cases hilast : i.val + 1 < n
  · have hindex : 2 * M + 1 + 2 * (M + 1) * i.val + 1 <
        n * (2 * (M + 1)) := by
      calc
        2 * M + 1 + 2 * (M + 1) * i.val + 1 =
            (i.val + 1) * (2 * (M + 1)) := by ring
        _ < n * (2 * (M + 1)) :=
          Nat.mul_lt_mul_of_pos_right hilast (by omega)
    rw [Nat.mod_eq_of_lt hindex, Fin.val_add_one_of_lt' hilast]
    ring
  · have hieq : i.val + 1 = n := by omega
    have hiwrap : (i + 1 : Fin n).val = 0 := by
      by_cases hnOne : n = 1
      · subst n
        have haddLt := (i + 1 : Fin 1).isLt
        omega
      · have honeLt : 1 < n := by omega
        have honeN : ((1 : Fin n).val) = 1 := by
          change 1 % n = 1
          exact Nat.mod_eq_of_lt honeLt
        rw [Fin.val_add, honeN, hieq, Nat.mod_self]
    rw [hiwrap]
    have hindex : 2 * M + 1 + 2 * (M + 1) * i.val + 1 =
        n * (2 * (M + 1)) := by
      calc
        2 * M + 1 + 2 * (M + 1) * i.val + 1 =
            (i.val + 1) * (2 * (M + 1)) := by ring
        _ = n * (2 * (M + 1)) := congrArg (fun r : ℕ ↦
          r * (2 * (M + 1))) hieq
    rw [hindex, Nat.mod_self]
    simp

@[simp] theorem KWStairParameterData.base_zero
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon) (i : Fin n) :
    data.base i 0 = polygon.vertex i := by
  simp [KWStairParameterData.base, data.parameter_zero]

@[simp] theorem KWStairParameterData.base_last
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon) (i : Fin n) :
    data.base i (Fin.last S) = polygon.vertex (i + 1) := by
  simp [KWStairParameterData.base, data.parameter_last]

theorem KWStairParameterData.vertex_odd_castSucc_succ
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (i : Fin n) (k : Fin M) :
    data.vertex (kwStairOddIndex i k.castSucc + 1) =
      data.base i k.succ.castSucc := by
  rw [kwStairOddIndex_castSucc_add_one]
  exact data.vertex_even i k.succ

theorem KWStairParameterData.vertex_odd_last_succ
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (i : Fin n) :
    data.vertex (kwStairOddIndex i (Fin.last M) + 1) =
      polygon.vertex (i + 1) := by
  rw [kwStairOddIndex_last_add_one, data.vertex_even]
  exact data.base_zero (i + 1)

theorem lineMap_sub_lineMap
    (a b : ℂ) (s t : ℝ) :
    AffineMap.lineMap a b t - AffineMap.lineMap a b s =
      (t - s) * (b - a) := by
  rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply]
  simp only [vsub_eq_sub, vadd_eq_add, Complex.real_smul]
  ring

theorem KWStairParameterData.corner_sub_base
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin S) :
    data.corner i k - data.base i k.castSucc =
      (data.parameter i k.succ - data.parameter i k.castSucc) *
        kwHorizontalPart (polygon.edgeVector i) := by
  simp [KWStairParameterData.corner]

theorem KWStairParameterData.base_succ_sub_corner
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin S) :
    data.base i k.succ - data.corner i k =
      (data.parameter i k.succ - data.parameter i k.castSucc) *
        kwVerticalPart (polygon.edgeVector i) := by
  have hbase : data.base i k.succ - data.base i k.castSucc =
      (data.parameter i k.succ - data.parameter i k.castSucc) *
        polygon.edgeVector i := by
    unfold KWStairParameterData.base KWFiniteSimplePolygon.edgeVector
    exact lineMap_sub_lineMap _ _ _ _
  calc
    data.base i k.succ - data.corner i k =
        (data.base i k.succ - data.base i k.castSucc) -
          (data.corner i k - data.base i k.castSucc) := by ring
    _ = (data.parameter i k.succ - data.parameter i k.castSucc) *
          polygon.edgeVector i -
        (data.parameter i k.succ - data.parameter i k.castSucc) *
          kwHorizontalPart (polygon.edgeVector i) := by
      rw [hbase, data.corner_sub_base]
    _ = (data.parameter i k.succ - data.parameter i k.castSucc) *
        kwVerticalPart (polygon.edgeVector i) := by
      have hdecomp := kwHorizontalPart_add_verticalPart
        (polygon.edgeVector i)
      have hdiff : polygon.edgeVector i -
          kwHorizontalPart (polygon.edgeVector i) =
          kwVerticalPart (polygon.edgeVector i) := by
        nth_rewrite 1 [← hdecomp]
        ring
      rw [← mul_sub, hdiff]

theorem KWStairParameterData.vertex_succ_sub_even
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin S) :
    data.vertex (kwStairEvenIndex i k + 1) -
        data.vertex (kwStairEvenIndex i k) =
      (data.parameter i k.succ - data.parameter i k.castSucc) *
        kwHorizontalPart (polygon.edgeVector i) := by
  rw [kwStairEvenIndex_add_one, data.vertex_odd, data.vertex_even]
  exact data.corner_sub_base i k

theorem KWStairParameterData.vertex_succ_sub_odd_castSucc
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (i : Fin n) (k : Fin M) :
    data.vertex (kwStairOddIndex i k.castSucc + 1) -
        data.vertex (kwStairOddIndex i k.castSucc) =
      (data.parameter i k.castSucc.succ -
          data.parameter i k.castSucc.castSucc) *
        kwVerticalPart (polygon.edgeVector i) := by
  rw [kwStairOddIndex_castSucc_add_one, data.vertex_even, data.vertex_odd]
  exact data.base_succ_sub_corner i k.castSucc

theorem KWStairParameterData.vertex_succ_sub_odd_last
    {n M : ℕ} [NeZero n]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := M + 1) polygon)
    (i : Fin n) :
    data.vertex (kwStairOddIndex i (Fin.last M) + 1) -
        data.vertex (kwStairOddIndex i (Fin.last M)) =
      (data.parameter i (Fin.last M).succ -
          data.parameter i (Fin.last M).castSucc) *
        kwVerticalPart (polygon.edgeVector i) := by
  rw [data.vertex_odd_last_succ, data.vertex_odd]
  have h := data.base_succ_sub_corner i (Fin.last M)
  have hlast : (Fin.last M).succ = Fin.last (M + 1) := by
    apply Fin.ext
    rfl
  rw [hlast, data.base_last] at h
  exact h

private theorem parameter_eq_of_coordinate_eq
    {a x s t : ℝ} (hx : x ≠ 0) (h : a + s * x = a + t * x) :
    s = t := by
  have hmul : s * x = t * x := add_left_cancel h
  exact mul_right_cancel₀ hx hmul



theorem KWStairParameterData.localVertex_injective
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) : Function.Injective (data.localVertex i) := by
  intro l r hlr
  obtain ⟨k, rfl | rfl⟩ := kwStairLocal_even_or_odd l
  · obtain ⟨q, rfl | rfl⟩ := kwStairLocal_even_or_odd r
    · have hre := congrArg Complex.re hlr
      simp only [data.localVertex_even, data.base_re] at hre
      have ht := parameter_eq_of_coordinate_eq (hcoords i).1 hre
      have hkq : k.castSucc = q.castSucc :=
        (data.parameter_strictMono i).injective ht
      have hkq' : k = q := Fin.castSucc_injective S hkq
      subst q
      rfl
    · have hre := congrArg Complex.re hlr
      have him := congrArg Complex.im hlr
      simp only [data.localVertex_even, data.localVertex_odd,
        data.base_re, data.corner_re] at hre
      simp only [data.localVertex_even, data.localVertex_odd,
        data.base_im, data.corner_im] at him
      have hright := parameter_eq_of_coordinate_eq (hcoords i).1 hre
      have hleft := parameter_eq_of_coordinate_eq (hcoords i).2 him
      have hstrict := data.parameter_strict i q
      linarith
  · obtain ⟨q, rfl | rfl⟩ := kwStairLocal_even_or_odd r
    · have hre := congrArg Complex.re hlr
      have him := congrArg Complex.im hlr
      simp only [data.localVertex_odd, data.localVertex_even,
        data.corner_re, data.base_re] at hre
      simp only [data.localVertex_odd, data.localVertex_even,
        data.corner_im, data.base_im] at him
      have hright := parameter_eq_of_coordinate_eq (hcoords i).1 hre
      have hleft := parameter_eq_of_coordinate_eq (hcoords i).2 him
      have hstrict := data.parameter_strict i k
      linarith
    · have him := congrArg Complex.im hlr
      simp only [data.localVertex_odd, data.corner_im] at him
      have ht := parameter_eq_of_coordinate_eq (hcoords i).2 him
      have hkq : k.castSucc = q.castSucc :=
        (data.parameter_strictMono i).injective ht
      have hkq' : k = q := Fin.castSucc_injective S hkq
      subst q
      rfl


def KWStairParameterData.MeshWithin
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon) (r : ℝ≥0) : Prop :=
  ∀ i : Fin n, ∀ k : Fin S,
    (data.parameter i k.succ - data.parameter i k.castSucc) *
      ‖polygon.edgeVector i‖ < r

theorem KWStairParameterData.parameter_mem_Icc
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin (S + 1)) :
    data.parameter i k ∈ Icc (0 : ℝ) 1 := by
  constructor
  · rw [← data.parameter_zero i]
    exact (data.parameter_strictMono i).monotone (Fin.zero_le k)
  · rw [← data.parameter_last i]
    exact (data.parameter_strictMono i).monotone (Fin.le_last k)

theorem KWStairParameterData.base_mem_closedEdge
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin (S + 1)) :
    data.base i k ∈ polygon.closedEdge i := by
  rw [KWFiniteSimplePolygon.closedEdge, segment_eq_image_lineMap]
  exact ⟨data.parameter i k, data.parameter_mem_Icc i k, rfl⟩

theorem KWStairParameterData.corner_mem_closedEdgeTube
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (r : ℝ≥0) (hfine : data.MeshWithin r)
    (i : Fin n) (k : Fin S) :
    data.corner i k ∈ polygon.closedEdgeTube r i := by
  refine ⟨data.base i k.castSucc, data.base_mem_closedEdge i k.castSucc, ?_⟩
  rw [dist_eq_norm, data.corner_sub_base, norm_mul,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hdelta : 0 < data.parameter i k.succ -
      data.parameter i k.castSucc := sub_pos.mpr (data.parameter_strict i k)
  rw [abs_of_pos hdelta]
  exact (mul_le_mul_of_nonneg_left
      (norm_kwHorizontalPart_le (polygon.edgeVector i)) hdelta.le).trans_lt
    (hfine i k)

theorem KWStairParameterData.localVertex_mem_closedEdgeTube
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (r : ℝ≥0) (hr : 0 < r) (hfine : data.MeshWithin r)
    (i : Fin n) (l : Fin (2 * S)) :
    data.localVertex i l ∈ polygon.closedEdgeTube r i := by
  obtain ⟨k, rfl | rfl⟩ := kwStairLocal_even_or_odd l
  · rw [data.localVertex_even]
    exact ⟨data.base i k.castSucc, data.base_mem_closedEdge i k.castSucc,
      by simpa only [dist_self, NNReal.coe_pos] using hr⟩
  · rw [data.localVertex_odd]
    exact data.corner_mem_closedEdgeTube r hfine i k

theorem KWStairParameterData.localVertex_ne_of_tubes_disjoint
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (r : ℝ≥0) (hr : 0 < r) (hfine : data.MeshWithin r)
    {i j : Fin n}
    (hdisjoint : Disjoint (polygon.closedEdgeTube r i)
      (polygon.closedEdgeTube r j))
    (l q : Fin (2 * S)) :
    data.localVertex i l ≠ data.localVertex j q := by
  intro heq
  have hi := data.localVertex_mem_closedEdgeTube r hr hfine i l
  have hj := data.localVertex_mem_closedEdgeTube r hr hfine j q
  rw [← heq] at hj
  exact Set.disjoint_left.mp hdisjoint hi hj



theorem KWStairParameterData.localVertex_ne_of_nonincident
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (r : ℝ≥0) (hr : 0 < r) (hfine : data.MeshWithin (r / 2))
    (hsep : ∀ i j : Fin n, KWEdgesNonincident i j →
      ∀ x ∈ polygon.closedEdge i, ∀ y ∈ polygon.closedEdge j,
        (r : ℝ) < dist x y)
    {i j : Fin n} (hij : KWEdgesNonincident i j)
    (l q : Fin (2 * S)) :
    data.localVertex i l ≠ data.localVertex j q := by
  have hhalf : 0 < r / 2 := half_pos hr
  exact data.localVertex_ne_of_tubes_disjoint (r / 2) hhalf hfine
    (polygon.closedEdgeTube_disjoint_of_nonincident hsep hij) l q



theorem KWFiniteSimplePolygon.exists_fine_endpointParameterData
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (r : ℝ≥0) (hr : 0 < r) :
    ∃ M : ℕ, ∃ beta : ℝ, ∃ alpha : Fin n → ℝ,
      ∃ data : KWStairParameterData (S := M + 2) polygon,
        0 < M ∧ 0 < beta ∧ beta < 1 / 4 ∧
        (∀ i, 0 < alpha i ∧ alpha i < beta) ∧
        (∀ i, |alpha i * (-polygon.edgeVector (i - 1)).re| <
          |beta * (polygon.edgeVector i).re|) ∧
        data.MeshWithin r := by
  obtain ⟨N, hmesh⟩ := polygon.exists_uniform_stair_mesh r hr
  let M : ℕ := N + 1
  have hM : 0 < M := by simp [M]
  let beta : ℝ := (8 * M : ℝ)⁻¹
  have hbeta : 0 < beta := by
    dsimp only [beta]
    positivity
  have hbetaQuarter : beta < 1 / 4 := by
    dsimp only [beta]
    have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hle : (8 * (M : ℝ))⁻¹ ≤ (8 : ℝ)⁻¹ := by
      apply (inv_le_inv₀ (by positivity) (by norm_num)).mpr
      nlinarith
    exact hle.trans_lt (by norm_num)
  obtain ⟨alpha, halpha⟩ := polygon.exists_incidentPatchScales
    hcoords beta beta hbeta hbeta
  have hsum (i : Fin n) : alpha i + beta < 1 := by
    have hai := (halpha i).2.1
    linarith [hbetaQuarter]
  let data := kwEndpointParameterData polygon M beta alpha hM hbeta
    (fun i ↦ (halpha i).1) hsum
  refine ⟨M, beta, alpha, data, hM, hbeta, hbetaQuarter,
    fun i ↦ ⟨(halpha i).1, (halpha i).2.1⟩,
    fun i ↦ (halpha i).2.2, ?_⟩
  intro i k
  have hbetaBound : beta ≤ (M : ℝ)⁻¹ := by
    dsimp only [beta]
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    have hMreal : 0 ≤ (M : ℝ) := by positivity
    nlinarith
  have halphaBound : alpha (i + 1) ≤ (M : ℝ)⁻¹ :=
    (le_of_lt (halpha (i + 1)).2.1).trans hbetaBound
  have hstep := kwEndpointParameter_step_le_inv M beta (alpha (i + 1))
    hM hbeta.le (halpha (i + 1)).1.le hbetaBound halphaBound k
  calc
    (data.parameter i k.succ - data.parameter i k.castSucc) *
        ‖polygon.edgeVector i‖ ≤
      (M : ℝ)⁻¹ * ‖polygon.edgeVector i‖ :=
        mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
    _ = ‖polygon.edgeVector i‖ / (N + 1 : ℝ) := by
      dsimp only [M]
      norm_num [div_eq_mul_inv, mul_comm]
    _ < r := hmesh i

end StatMech.FrontierA
