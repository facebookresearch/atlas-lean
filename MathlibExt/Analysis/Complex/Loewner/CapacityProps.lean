/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.Complex.Loewner.LoewnerProps

/-!
# Properties of half-plane capacity

A map `g : ℂ → ℂ` has half-plane capacity `a` (`StatMech.SLE.HasHalfPlaneCapacity g a`) when
`g(z) = z + a/z + o(1/z)` at infinity. This file proves that capacities add under composition in
the form `a ≤ a'` when `g' = h ∘ g` and `hcap h ≥ 0`, scale as `r²` under `z ↦ r g(z/r)`, are
invariant under real translation conjugation, and computes the capacity `c` of `z ↦ z + c/z` (the
half-disk map when `c ≥ 0`). Additivity itself is `StatMech.SLE.hasHalfPlaneCapacity_comp` in
`MathlibExt.Analysis.Complex.Loewner.LoewnerProps`.

## Main results

* `StatMech.SLE.HasHalfPlaneCapacity.le_of_comp`: monotonicity under composition.
* `StatMech.SLE.HasHalfPlaneCapacity.scale`: `hcap(r g(·/r)) = r² hcap g`.
* `StatMech.SLE.HasHalfPlaneCapacity.translate`.
* `StatMech.SLE.hasHalfPlaneCapacity_halfDisk`: `hcap(z + c/z) = c`.
* `StatMech.SLE.hasHalfPlaneCapacity_neg_example`: `z - 1/z` has capacity `-1`, so the
  normalization alone does not force nonnegative capacity.

## References

* G. F. Lawler, *Conformally Invariant Processes in the Plane*, AMS (2005), Section 3.4.
-/

@[expose] public section

open scoped UpperHalfPlane NNReal
open Filter Topology Complex Bornology

namespace StatMech.SLE

/-- `f` tends to infinity along `l` iff `‖f‖` tends to `+∞`. -/
theorem tendsto_cocompact_iff_norm (l : Filter ℂ) (f : ℂ → ℂ) :
    Tendsto f l (cocompact ℂ) ↔ Tendsto (fun z => ‖f z‖) l atTop := by
  rw [← Metric.cobounded_eq_cocompact (α := ℂ), ← comap_norm_atTop (E := ℂ), tendsto_comap_iff]
  rfl

/-- `z⁻¹ → 0` as `z → ∞`. See also Mathlib's `tendsto_inv₀_cobounded`. -/
theorem tendsto_inv_cocompact : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (nhds 0) := by
  have hz : Tendsto (fun z : ℂ => ‖z‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_inv]
  exact hz.inv_tendsto_atTop

/-- `z / r → ∞` as `z → ∞`, for `r ≠ 0`. -/
theorem tendsto_div_cocompact {r : ℂ} (hr : r ≠ 0) :
    Tendsto (fun z : ℂ => z / r) (cocompact ℂ) (cocompact ℂ) := by
  have : (fun z : ℂ => z / r) = (fun z => r⁻¹ * z) := by funext z; rw [div_eq_inv_mul]
  rw [this]
  exact Filter.tendsto_cocompact_mul_left₀ (inv_ne_zero hr)

/-- `z + c → ∞` as `z → ∞`. -/
theorem tendsto_translate_cocompact (c : ℂ) :
    Tendsto (fun z : ℂ => z + c) (cocompact ℂ) (cocompact ℂ) := by
  rw [tendsto_cocompact_iff_norm]
  have hz : Tendsto (fun z : ℂ => ‖z‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
  have hlow : Tendsto (fun z : ℂ => ‖z‖ - ‖c‖) (cocompact ℂ) atTop := by
    simpa [sub_eq_add_neg] using hz.atTop_add (tendsto_const_nhds (x := -‖c‖))
  refine tendsto_atTop_mono (fun z => ?_) hlow
  have : ‖z‖ ≤ ‖z + c‖ + ‖c‖ := by
    calc ‖z‖ = ‖(z + c) - c‖ := by ring_nf
      _ ≤ ‖z + c‖ + ‖c‖ := norm_sub_le _ _
  linarith

/-- `z - z⁻¹` has half-plane capacity `-1`: the normalization at infinity does not by itself make
the capacity nonnegative. -/
theorem hasHalfPlaneCapacity_neg_example : HasHalfPlaneCapacity (fun z => z - z⁻¹) (-1) := by
  constructor
  · have hfun : (fun z : ℂ => (z - z⁻¹) - z) = (fun z => (-1 : ℂ) * z⁻¹) := by
      funext z; ring
    rw [hfun]; simpa using tendsto_inv_cocompact.const_mul (-1 : ℂ)
  · have hfun : (fun z : ℂ => z * ((z - z⁻¹) - z)) =ᶠ[cocompact ℂ] (fun _ => ((-1 : ℝ) : ℂ)) := by
      filter_upwards [eventually_ne_zero_cocompact] with z hz
      push_cast; field_simp; ring
    rw [tendsto_congr' hfun]; exact tendsto_const_nhds

/-- If `g' = h ∘ g` with `hcap g = a`, `hcap h = b ≥ 0` and `hcap g' = a'`, then `a ≤ a'`. -/
theorem HasHalfPlaneCapacity.le_of_comp {g h g' : ℂ → ℂ} {a b a' : ℝ}
    (hg : HasHalfPlaneCapacity g a) (hh : HasHalfPlaneCapacity h b)
    (hb : 0 ≤ b) (hfac : g' = h ∘ g) (hg' : HasHalfPlaneCapacity g' a') :
    a ≤ a' := by
  have hcomp : HasHalfPlaneCapacity g' (a + b) := hfac ▸ hasHalfPlaneCapacity_comp hg hh
  have : a' = a + b := hg'.unique hcomp
  rw [this]; linarith

/-- Scaling: `z ↦ r g(z/r)` has half-plane capacity `r² a` when `g` has capacity `a` (`r ≠ 0`). -/
theorem HasHalfPlaneCapacity.scale {g : ℂ → ℂ} {a : ℝ} {r : ℝ} (hr : r ≠ 0)
    (hg : HasHalfPlaneCapacity g a) :
    HasHalfPlaneCapacity (fun z => (r : ℂ) * g (z / r)) (r ^ 2 * a) := by
  obtain ⟨h0, ha⟩ := hg
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hcc : Tendsto (fun z : ℂ => z / (r : ℂ)) (cocompact ℂ) (cocompact ℂ) :=
    tendsto_div_cocompact hrc
  refine ⟨?_, ?_⟩
  · have hfun : (fun z => (r : ℂ) * g (z / r) - z)
        = (fun z => (r : ℂ) * (g (z / (r : ℂ)) - z / (r : ℂ))) := by
      funext z; field_simp
    rw [hfun]
    have e1 : Tendsto (fun z => g (z / (r : ℂ)) - z / (r : ℂ)) (cocompact ℂ) (nhds 0) := by
      simpa [Function.comp_def] using h0.comp hcc
    simpa using e1.const_mul (r : ℂ)
  · have e2 : Tendsto (fun z => (z / (r : ℂ)) * (g (z / (r : ℂ)) - z / (r : ℂ)))
        (cocompact ℂ) (nhds (a : ℂ)) := by
      simpa [Function.comp_def] using ha.comp hcc
    have hfun : (fun z => z * ((r : ℂ) * g (z / r) - z))
        = (fun z => (r : ℂ) ^ 2 * ((z / (r : ℂ)) * (g (z / (r : ℂ)) - z / (r : ℂ)))) := by
      funext z; field_simp
    rw [hfun]
    have hcast : (((r ^ 2 * a : ℝ)) : ℂ) = (r : ℂ) ^ 2 * (a : ℂ) := by push_cast; ring
    rw [hcast]
    exact e2.const_mul ((r : ℂ) ^ 2)

/-- Translation: `z ↦ g(z - c) + c` has the same half-plane capacity as `g`. -/
theorem HasHalfPlaneCapacity.translate {g : ℂ → ℂ} {a : ℝ} (c : ℂ)
    (hg : HasHalfPlaneCapacity g a) :
    HasHalfPlaneCapacity (fun z => g (z - c) + c) a := by
  obtain ⟨h0, ha⟩ := hg
  have hcc : Tendsto (fun z : ℂ => z - c) (cocompact ℂ) (cocompact ℂ) := by
    simpa [sub_eq_add_neg] using tendsto_translate_cocompact (-c)
  have e0 : Tendsto (fun z => g (z - c) - (z - c)) (cocompact ℂ) (nhds 0) := by
    simpa [Function.comp_def] using h0.comp hcc
  refine ⟨?_, ?_⟩
  · have hfun : (fun z => (g (z - c) + c) - z) = (fun z => g (z - c) - (z - c)) := by
      funext z; ring
    rw [hfun]; exact e0
  · have e2 : Tendsto (fun z => (z - c) * (g (z - c) - (z - c))) (cocompact ℂ) (nhds (a : ℂ)) := by
      simpa [Function.comp_def] using ha.comp hcc
    have e3 : Tendsto (fun z => c * (g (z - c) - (z - c))) (cocompact ℂ) (nhds 0) := by
      simpa using e0.const_mul c
    have hsum := e2.add e3
    have hfun : (fun z => z * ((g (z - c) + c) - z))
        = (fun z => (z - c) * (g (z - c) - (z - c)) + c * (g (z - c) - (z - c))) := by
      funext z; ring
    rw [hfun]; simpa using hsum

/-- `z ↦ z + c/z` has half-plane capacity `c`; for `c = r² ≥ 0` it is the normalized map
removing the half-disk of radius `r`. -/
theorem hasHalfPlaneCapacity_halfDisk (c : ℝ) :
    HasHalfPlaneCapacity (fun z => z + (c : ℂ) / z) c := by
  refine ⟨?_, ?_⟩
  · have hfun : (fun z : ℂ => (z + (c : ℂ) / z) - z) = (fun z => (c : ℂ) * z⁻¹) := by
      funext z; rw [div_eq_mul_inv]; ring
    rw [hfun]; simpa using tendsto_inv_cocompact.const_mul (c : ℂ)
  · have hfun : (fun z : ℂ => z * ((z + (c : ℂ) / z) - z)) =ᶠ[cocompact ℂ] (fun _ => (c : ℂ)) := by
      filter_upwards [eventually_ne_zero_cocompact] with z hz
      field_simp; ring
    rw [tendsto_congr' hfun]; exact tendsto_const_nhds

/-- Uniqueness: the half-plane capacity of `z ↦ z + c/z` is `c`. -/
theorem halfDisk_capacity_eq {c a : ℝ}
    (h : HasHalfPlaneCapacity (fun z => z + (c : ℂ) / z) a) : a = c :=
  h.unique (hasHalfPlaneCapacity_halfDisk c)

/-- Scaling the unit half-disk map by `r` gives capacity `r² · 1`. -/
theorem halfDisk_scale_consistent {r : ℝ} (hr : r ≠ 0) :
    HasHalfPlaneCapacity (fun z => (r : ℂ) * ((z / r) + (1 : ℂ) / (z / r))) (r ^ 2 * 1) := by
  have h := (hasHalfPlaneCapacity_halfDisk 1).scale hr
  refine ⟨?_, ?_⟩
  · exact h.1
  · exact h.2

/-- The scaled unit half-disk map is `z ↦ z + r²/z` (for `z ≠ 0`). -/
theorem halfDisk_scale_eq_formula {r : ℝ} (hr : r ≠ 0) {z : ℂ} (hz : z ≠ 0) :
    (r : ℂ) * ((z / r) + (1 : ℂ) / (z / r)) = z + ((r ^ 2 : ℝ) : ℂ) / z := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  push_cast
  field_simp

/-- Composition with the identity on the right adds `0`. See also
`StatMech.SLE.hasHalfPlaneCapacity_comp_id_right` (conclusion `a` instead of `0 + a`). -/
theorem HasHalfPlaneCapacity.comp_id {g : ℂ → ℂ} {a : ℝ} (hg : HasHalfPlaneCapacity g a) :
    HasHalfPlaneCapacity (g ∘ id) (0 + a) :=
  hasHalfPlaneCapacity_comp hasHalfPlaneCapacity_id hg

/-- Composition with the identity on the left adds `0`. See also
`StatMech.SLE.hasHalfPlaneCapacity_comp_id_left` (conclusion `a` instead of `a + 0`). -/
theorem HasHalfPlaneCapacity.id_comp {g : ℂ → ℂ} {a : ℝ} (hg : HasHalfPlaneCapacity g a) :
    HasHalfPlaneCapacity (id ∘ g) (a + 0) :=
  hasHalfPlaneCapacity_comp hg hasHalfPlaneCapacity_id

end StatMech.SLE
