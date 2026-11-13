/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib










namespace StatMech
namespace Exact3D


structure ExpUpperBound (q r : ℝ) : Prop where
  bound : Real.exp q ≤ r



structure LogUpperBound (x u : ℝ) : Prop where
  x_pos : 0 < x
  bound : Real.log x ≤ u



structure LogLowerBound (l x : ℝ) : Prop where
  x_pos : 0 < x
  bound : l ≤ Real.log x


abbrev RatExpUpperBound (q r : ℚ) : Prop :=
  ExpUpperBound (q : ℝ) (r : ℝ)


abbrev RatLogUpperBound (x u : ℚ) : Prop :=
  LogUpperBound (x : ℝ) (u : ℝ)


abbrev RatLogLowerBound (l x : ℚ) : Prop :=
  LogLowerBound (l : ℝ) (x : ℝ)

@[simp] theorem expUpperBound_iff {q r : ℝ} :
    ExpUpperBound q r ↔ Real.exp q ≤ r := by
  constructor
  · exact fun h => h.bound
  · exact fun h => ⟨h⟩

@[simp] theorem logUpperBound_iff {x u : ℝ} :
    LogUpperBound x u ↔ 0 < x ∧ Real.log x ≤ u := by
  constructor
  · exact fun h => ⟨h.x_pos, h.bound⟩
  · exact fun h => ⟨h.1, h.2⟩

@[simp] theorem logLowerBound_iff {l x : ℝ} :
    LogLowerBound l x ↔ 0 < x ∧ l ≤ Real.log x := by
  constructor
  · exact fun h => ⟨h.x_pos, h.bound⟩
  · exact fun h => ⟨h.1, h.2⟩


theorem log_le_of_le_exp {x u : ℝ} (hx : 0 < x) (hxu : x ≤ Real.exp u) :
    Real.log x ≤ u :=
  (Real.log_le_iff_le_exp hx).mpr hxu



theorem le_exp_of_log_le {x u : ℝ} (hx : 0 < x) (hxu : Real.log x ≤ u) :
    x ≤ Real.exp u :=
  (Real.log_le_iff_le_exp hx).mp hxu


theorem le_log_of_exp_le {l x : ℝ} (hlx : Real.exp l ≤ x) :
    l ≤ Real.log x := by
  have hx : 0 < x := lt_of_lt_of_le (Real.exp_pos l) hlx
  exact (Real.le_log_iff_exp_le hx).mpr hlx



theorem exp_le_of_le_log {l x : ℝ} (hx : 0 < x) (hlx : l ≤ Real.log x) :
    Real.exp l ≤ x :=
  (Real.le_log_iff_exp_le hx).mp hlx



theorem log_le_of_le_of_log_le {x y u : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hyu : Real.log y ≤ u) :
    Real.log x ≤ u :=
  le_trans (Real.log_le_log hx hxy) hyu



theorem le_log_of_le_of_le_log {l x y : ℝ}
    (hx : 0 < x) (hxy : x ≤ y) (hlx : l ≤ Real.log x) :
    l ≤ Real.log y :=
  le_trans hlx (Real.log_le_log hx hxy)

namespace ExpUpperBound

theorem rhs_pos {q r : ℝ} (h : ExpUpperBound q r) : 0 < r :=
  lt_of_lt_of_le (Real.exp_pos q) h.bound

theorem rhs_nonneg {q r : ℝ} (h : ExpUpperBound q r) : 0 ≤ r :=
  h.rhs_pos.le


theorem mono_left {p q r : ℝ} (hpq : p ≤ q) (h : ExpUpperBound q r) :
    ExpUpperBound p r where
  bound := le_trans (Real.exp_le_exp.mpr hpq) h.bound


theorem trans_right {q r s : ℝ} (h : ExpUpperBound q r) (hrs : r ≤ s) :
    ExpUpperBound q s where
  bound := le_trans h.bound hrs



theorem toLogLowerBound {q r : ℝ} (h : ExpUpperBound q r) :
    LogLowerBound q r where
  x_pos := h.rhs_pos
  bound := le_log_of_exp_le h.bound

end ExpUpperBound

namespace LogUpperBound


theorem mono_left {x y u : ℝ} (hy : 0 < y) (hyx : y ≤ x)
    (h : LogUpperBound x u) :
    LogUpperBound y u where
  x_pos := hy
  bound := log_le_of_le_of_log_le hy hyx h.bound


theorem trans_right {x u v : ℝ} (h : LogUpperBound x u) (huv : u ≤ v) :
    LogUpperBound x v where
  x_pos := h.x_pos
  bound := le_trans h.bound huv


theorem le_exp {x u : ℝ} (h : LogUpperBound x u) :
    x ≤ Real.exp u :=
  le_exp_of_log_le h.x_pos h.bound



theorem of_le_exp {x u : ℝ} (hx : 0 < x) (hxu : x ≤ Real.exp u) :
    LogUpperBound x u where
  x_pos := hx
  bound := log_le_of_le_exp hx hxu

end LogUpperBound

namespace LogLowerBound


theorem trans_left {k l x : ℝ} (hkl : k ≤ l) (h : LogLowerBound l x) :
    LogLowerBound k x where
  x_pos := h.x_pos
  bound := le_trans hkl h.bound


theorem mono_right {l x y : ℝ} (h : LogLowerBound l x) (hxy : x ≤ y) :
    LogLowerBound l y where
  x_pos := lt_of_lt_of_le h.x_pos hxy
  bound := le_log_of_le_of_le_log h.x_pos hxy h.bound


theorem exp_le {l x : ℝ} (h : LogLowerBound l x) :
    Real.exp l ≤ x :=
  exp_le_of_le_log h.x_pos h.bound



theorem of_exp_le {l x : ℝ} (hlx : Real.exp l ≤ x) :
    LogLowerBound l x where
  x_pos := lt_of_lt_of_le (Real.exp_pos l) hlx
  bound := le_log_of_exp_le hlx


theorem toExpUpperBound {l x : ℝ} (h : LogLowerBound l x) :
    ExpUpperBound l x where
  bound := h.exp_le

end LogLowerBound

@[simp] theorem expUpperBound_zero_one : ExpUpperBound 0 1 where
  bound := by simp

@[simp] theorem logUpperBound_one_zero : LogUpperBound 1 0 where
  x_pos := zero_lt_one
  bound := by simp

@[simp] theorem logLowerBound_zero_one : LogLowerBound 0 1 where
  x_pos := zero_lt_one
  bound := by simp

end Exact3D
end StatMech
