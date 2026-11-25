/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.InfiniteClusterCount

/-!
# Removing a lattice site from a bond configuration

Closing all edges incident to a site gives a measurable operation on configurations. It
commutes with lattice translations, and connectivity after site removal is a measurable event.
-/

@[expose] public section

open MeasureTheory StatMech.Lattice StatMech.ConfigSpace

namespace StatMech.Percolation

variable {d : ℕ}

/-- The configuration obtained from `ω` by closing every edge incident to `x`. -/
noncomputable def removeSite (x : Site d) (ω : ConfigSpace (Sym2 (Site d))) :
    ConfigSpace (Sym2 (Site d)) :=
  fun e => if x ∈ e then false else ω e

@[simp] lemma removeSite_apply_of_mem {x : Site d} {e : Sym2 (Site d)} (h : x ∈ e)
    (ω : ConfigSpace (Sym2 (Site d))) : removeSite x ω e = false := by
  simp [removeSite, h]

@[simp] lemma removeSite_apply_of_notMem {x : Site d} {e : Sym2 (Site d)} (h : x ∉ e)
    (ω : ConfigSpace (Sym2 (Site d))) : removeSite x ω e = ω e := by
  simp [removeSite, h]

lemma measurable_removeSite (x : Site d) :
    Measurable (fun ω : ConfigSpace (Sym2 (Site d)) => removeSite x ω) := by
  apply Measurable.of_eval
  intro e
  unfold removeSite
  by_cases h : x ∈ e
  · simp [h]
  · simp only [h, ite_false]; exact measurable_pi_apply e

lemma removeSite_shift (g : Multiplicative (Site d)) (x : Site d)
    (ω : ConfigSpace (Sym2 (Site d))) :
    removeSite (g • x) (shift g ω) = shift g (removeSite x ω) := by
  funext e
  unfold removeSite
  rw [shift_apply, shift_apply]
  have hmem : (g • x ∈ e) ↔ (x ∈ g⁻¹ • e) := by
    constructor
    · intro h
      have : g⁻¹ • (g • x) ∈ g⁻¹ • e := Sym2.mem_map.mpr ⟨g • x, h, rfl⟩
      rwa [inv_smul_smul] at this
    · intro h
      have : g • x ∈ g • (g⁻¹ • e) := Sym2.mem_map.mpr ⟨x, h, rfl⟩
      rwa [smul_inv_smul] at this
  by_cases h : g • x ∈ e
  · rw [ite_eq_left h, ite_eq_left (hmem.mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun hc => h (hmem.mpr hc))]

lemma measurableSet_connected_removeSite (x a b : Site d) :
    MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | Connected d (removeSite x ω) a b} := by
  have h : {ω : ConfigSpace (Sym2 (Site d)) | Connected d (removeSite x ω) a b}
      = (fun ω => removeSite x ω) ⁻¹' {ω' | Connected d ω' a b} := rfl
  rw [h]
  exact (measurable_removeSite x) (measurableSet_connected a b)

end StatMech.Percolation
