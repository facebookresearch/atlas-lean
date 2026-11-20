/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































































import Code.Universality.HexConcreteRegion
import Code.Universality.HexBoundaryAssign

namespace StatMech.Universality

open Complex
open HexWalk
open scoped BigOperators















theorem hexStrip_vert_eq_mid_plus_step (m : ℂ) (h : ℤ) (ts : List ℤ) :
    ∀ x ∈ verticesAux m h ts, ∃ mm ∈ midsAux m h ts, ∃ hh : ℤ, x = mm + halfStep hh := by
  induction ts generalizing m h with
  | nil =>
    intro x hx
    simp only [verticesAux_nil, List.mem_singleton] at hx
    exact ⟨m, by simp [midsAux_nil], h, hx⟩
  | cons t ts ih =>
    intro x hx
    rw [verticesAux_cons, List.mem_cons] at hx
    rcases hx with hx | hx
    · exact ⟨m, by simp [midsAux_cons], h, hx⟩
    · obtain ⟨mm, hmm, hh, hxe⟩ := ih (m + halfStep h + halfStep (h + t)) (h + t) x hx
      exact ⟨mm, by rw [midsAux_cons, List.mem_cons]; exact Or.inr hmm, hh, hxe⟩




theorem hexStrip_vertex_mem_eq (w : HexWalk) :
    ∀ x ∈ w.vertices, ∃ mm ∈ w.mids, ∃ hh : ℤ, x = mm + halfStep hh := by
  intro x hx
  exact hexStrip_vert_eq_mid_plus_step w.startMid w.h0 w.turns x hx











theorem hexStrip_halfStep_add6 (h : ℤ) : halfStep (h + 6) = halfStep h := by
  unfold halfStep
  rw [show (h + 6 : ℤ) = (h + 3) + 3 by ring, hexUnit_add_three, hexUnit_add_three]; ring




theorem hexStrip_halfStep_mod6 (h : ℤ) : halfStep h = halfStep (h % 6) := by
  have hper6 : ∀ (x : ℤ) (k : ℤ), halfStep (x + 6 * k) = halfStep x := by
    intro x k
    induction k using Int.induction_on with
    | zero => simp
    | succ n ih =>
        rw [show x + 6 * ((n : ℤ) + 1) = (x + 6 * (n : ℤ)) + 6 by ring, hexStrip_halfStep_add6]
        exact ih
    | pred n ih =>
        have hh : halfStep ((x + 6 * (-(n : ℤ) - 1)) + 6) = halfStep (x + 6 * (-(n : ℤ) - 1)) :=
          hexStrip_halfStep_add6 _
        rw [show (x + 6 * (-(n : ℤ) - 1)) + 6 = x + 6 * (-(n : ℤ)) by ring] at hh
        rw [← hh]; exact ih
  conv_lhs => rw [show h = (h % 6) + 6 * (h / 6) by omega]
  rw [hper6]











@[simp]
theorem hexStrip_norm_halfStep (h : ℤ) : ‖halfStep h‖ = 1 / 2 := by
  unfold halfStep
  rw [norm_mul, norm_hexUnit, mul_one]
  norm_num




theorem hexStrip_dist_vert_mid (mm : ℂ) (hh : ℤ) : dist (mm + halfStep hh) mm = 1 / 2 := by
  rw [Complex.dist_eq, add_sub_cancel_left, hexStrip_norm_halfStep]













noncomputable def hexStrip_verts (M : Finset ℂ) : Finset ℂ :=
  M.biUnion (fun mm => {mm + halfStep 0, mm + halfStep 1, mm + halfStep 2,
    mm + halfStep 3, mm + halfStep 4, mm + halfStep 5})



theorem hexStrip_mem_verts (M : Finset ℂ) {mm : ℂ} (hmm : mm ∈ M) (hh : ℤ) :
    mm + halfStep hh ∈ hexStrip_verts M := by
  unfold hexStrip_verts
  rw [Finset.mem_biUnion]
  refine ⟨mm, hmm, ?_⟩
  rw [hexStrip_halfStep_mod6 hh]
  have h0 : 0 ≤ hh % 6 := Int.emod_nonneg hh (by norm_num)
  have h6 : hh % 6 < 6 := Int.emod_lt_of_pos hh (by norm_num)
  interval_cases (hh % 6) <;> simp




















theorem hexStrip_vertexBound (M : Finset ℂ) (w : HexWalk)
    (hstay : ∀ m ∈ w.mids, m ∈ M) :
    ∀ x ∈ w.vertices, x ∈ hexStrip_verts M := by
  intro x hx
  obtain ⟨mm, hmm, hh, hxe⟩ := hexStrip_vertex_mem_eq w x hx
  rw [hxe]
  exact hexStrip_mem_verts M (hstay mm hmm) hh













noncomputable def hexStrip_finiteRegion (M : Finset ℂ) (a : ℂ) (ha : a ∈ M) :
    HexFiniteRegion where
  verts := hexStrip_verts M
  mids := M
  start := a
  start_mem := ha
  vertexBound := hexStrip_vertexBound M

@[simp] theorem hexStrip_finiteRegion_mids (M : Finset ℂ) (a : ℂ) (ha : a ∈ M) :
    (hexStrip_finiteRegion M a ha).mids = M := rfl

@[simp] theorem hexStrip_finiteRegion_verts (M : Finset ℂ) (a : ℂ) (ha : a ∈ M) :
    (hexStrip_finiteRegion M a ha).verts = hexStrip_verts M := rfl

@[simp] theorem hexStrip_finiteRegion_start (M : Finset ℂ) (a : ℂ) (ha : a ∈ M) :
    (hexStrip_finiteRegion M a ha).start = a := rfl


theorem hexStrip_finiteRegion_inRegion_iff (M : Finset ℂ) (a : ℂ) (ha : a ∈ M) (z : ℂ) :
    (hexStrip_finiteRegion M a ha).inRegion z ↔ z ∈ M := Iff.rfl





theorem hexStrip_finiteRegion_length_lt (M : Finset ℂ) (a : ℂ) (ha : a ∈ M)
    (h0 : ℤ) (ts : List ℤ)
    (hsaw : (ofTurns a h0 ts).IsSAW)
    (hstay : (ofTurns a h0 ts).StaysIn (hexStrip_finiteRegion M a ha).inRegion) :
    ts.length < (hexStrip_verts M).card := by
  have := (hexStrip_finiteRegion M a ha).length_lt a h0 ts hsaw hstay
  rwa [hexStrip_finiteRegion_verts] at this













theorem hexStrip_vertexBound_of_superset (M : Finset ℂ) (verts : Finset ℂ)
    (hsub : hexStrip_verts M ⊆ verts) (w : HexWalk)
    (hstay : ∀ m ∈ w.mids, m ∈ M) :
    ∀ x ∈ w.vertices, x ∈ verts :=
  fun x hx => hsub (hexStrip_vertexBound M w hstay x hx)







noncomputable def hexStrip_finiteRegion_of_superset (M verts : Finset ℂ) (a : ℂ)
    (ha : a ∈ M) (hsub : hexStrip_verts M ⊆ verts) :
    HexFiniteRegion where
  verts := verts
  mids := M
  start := a
  start_mem := ha
  vertexBound := hexStrip_vertexBound_of_superset M verts hsub

@[simp] theorem hexStrip_finiteRegion_of_superset_verts (M verts : Finset ℂ) (a : ℂ)
    (ha : a ∈ M) (hsub : hexStrip_verts M ⊆ verts) :
    (hexStrip_finiteRegion_of_superset M verts a ha hsub).verts = verts := rfl

@[simp] theorem hexStrip_finiteRegion_of_superset_mids (M verts : Finset ℂ) (a : ℂ)
    (ha : a ∈ M) (hsub : hexStrip_verts M ⊆ verts) :
    (hexStrip_finiteRegion_of_superset M verts a ha hsub).mids = M := rfl












def hexStrip_inStrip (R : HexRegion) (z : ℂ) : Prop :=
  0 ≤ z.re ∧ z.re ≤ R.width ∧ Real.sqrt 3 * |z.im| ≤ R.slant + z.re








noncomputable def hexStrip_region_finiteRegion (R : HexRegion) (M : Finset ℂ)
    (ha : R.start ∈ M) : HexFiniteRegion :=
  hexStrip_finiteRegion M R.start ha

@[simp] theorem hexStrip_region_finiteRegion_mids (R : HexRegion) (M : Finset ℂ)
    (ha : R.start ∈ M) : (hexStrip_region_finiteRegion R M ha).mids = M := rfl

@[simp] theorem hexStrip_region_finiteRegion_start (R : HexRegion) (M : Finset ℂ)
    (ha : R.start ∈ M) : (hexStrip_region_finiteRegion R M ha).start = R.start := rfl

@[simp] theorem hexStrip_region_finiteRegion_verts (R : HexRegion) (M : Finset ℂ)
    (ha : R.start ∈ M) : (hexStrip_region_finiteRegion R M ha).verts = hexStrip_verts M := rfl












theorem hexStrip_single_closure (a : ℂ) (w : HexWalk)
    (hstay : ∀ m ∈ w.mids, m ∈ ({a} : Finset ℂ)) :
    ∀ x ∈ w.vertices, x ∈ hexStrip_verts ({a} : Finset ℂ) :=
  hexStrip_vertexBound ({a} : Finset ℂ) w hstay





noncomputable def hexStrip_singleRegion (a : ℂ) : HexFiniteRegion :=
  hexStrip_finiteRegion ({a} : Finset ℂ) a (Finset.mem_singleton_self a)

@[simp] theorem hexStrip_singleRegion_mids (a : ℂ) :
    (hexStrip_singleRegion a).mids = ({a} : Finset ℂ) := rfl

@[simp] theorem hexStrip_singleRegion_start (a : ℂ) :
    (hexStrip_singleRegion a).start = a := rfl

end StatMech.Universality
