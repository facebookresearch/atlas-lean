/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































































import Mathlib
import Code.FK.BoxFeketePerVolume
import Code.FK.CenteredFreeEnergy
import Code.FK.FKInterfaceSubadd
import Code.FK.EdgeConfigZ

open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace StatMech

namespace Walls

















theorem fc_doublingStep_div (a A c i e E K : ℝ) (he : 0 < e) (hE : 0 < E)
    (hdoub : A ≤ K * a + i * c) (hedge : |K * e - E| ≤ i) :
    A / E - a / e ≤ (|a| / e + c) * (i / E) := by
  have heE : 0 < E * e := mul_pos hE he
  
  have h1 : A / E ≤ (K * a + i * c) / E := (div_le_div_iff_of_pos_right hE).mpr hdoub
  
  have hid : (K * a + i * c) / E - a / e
      = a * (K * e - E) / (E * e) + c * (i / E) := by
    field_simp; ring
  
  have h2 : a * (K * e - E) / (E * e) ≤ (|a| / e) * (i / E) := by
    rw [div_le_iff₀ heE]
    have hrhs : (|a| / e) * (i / E) * (E * e) = |a| * i := by field_simp
    rw [hrhs]
    calc a * (K * e - E) ≤ |a * (K * e - E)| := le_abs_self _
      _ = |a| * |K * e - E| := abs_mul _ _
      _ ≤ |a| * i := mul_le_mul_of_nonneg_left hedge (abs_nonneg _)
  
  calc A / E - a / e ≤ (K * a + i * c) / E - a / e := by linarith
    _ = a * (K * e - E) / (E * e) + c * (i / E) := hid
    _ ≤ (|a| / e) * (i / E) + c * (i / E) := by linarith
    _ = (|a| / e + c) * (i / E) := by ring


















theorem fc_doublingStep (a A c i e E K C : ℝ) (he : 0 < e) (hE : 0 < E)
    (hdoub : A ≤ K * a + i * c) (hedge : |K * e - E| ≤ i) :
    (-a / e + C) - (|a| / e + c) * (i / E) ≤ (-A / E + C) := by
  have hcore := fc_doublingStep_div a A c i e E K he hE hdoub hedge
  have e1 : -a / e = -(a / e) := by ring
  have e2 : -A / E = -(A / E) := by ring
  rw [e1, e2]; linarith










theorem fc_doublingStep_freeEnergy (a A c i e E K C : ℝ) (he : 0 < e) (hE : 0 < E)
    (hdoub : A ≤ K * a + i * c) (hedge : |K * e - E| ≤ i) :
    (fun (Ec u : ℝ) => -u / Ec + C) e a - (|a| / e + c) * (i / E)
      ≤ (fun (Ec u : ℝ) => -u / Ec + C) E A := by
  simpa using fc_doublingStep a A c i e E K C he hE hdoub hedge













theorem fc_deficit_nonneg (a c i e E : ℝ) (he : 0 < e) (hE : 0 < E) (hc : 0 ≤ c)
    (hi : 0 ≤ i) :
    0 ≤ (|a| / e + c) * (i / E) := by positivity











theorem fc_doublingStep_satisfiable (a e K C : ℝ) (he : 0 < e) (hK : 0 < K) :
    let A := K * a; let E := K * e
    
    (A ≤ K * a + (0 : ℝ) * (0 : ℝ))
      
      ∧ (|K * e - E| ≤ (0 : ℝ))
      
      ∧ ((|a| / e + (0 : ℝ)) * ((0 : ℝ) / E) = 0)
      
      ∧ ((-a / e + C) - (|a| / e + (0 : ℝ)) * ((0 : ℝ) / E) ≤ (-A / E + C)) := by
  intro A E
  have hE : 0 < E := mul_pos hK he
  refine ⟨by simp [A], by simp [E], by simp, ?_⟩
  
  have := fc_doublingStep a A 0 0 e E K C he hE (by simp [A]) (by simp [E])
  simpa using this

end Walls

end StatMech
