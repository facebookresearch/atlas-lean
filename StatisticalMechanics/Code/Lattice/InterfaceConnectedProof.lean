/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartInjective
import Code.Lattice.DartOrbit
import Code.Lattice.InterfaceOrbit
import Code.Lattice.InterfaceConnected

open SimpleGraph Function

namespace StatMech

namespace Lattice








noncomputable def facingDart (v g : Site 2) (hg : unitWt g = 1) : Dart := mkDart (v - g) g hg

@[simp] theorem facingDart_head (v g : Site 2) (hg : unitWt g = 1) :
    (facingDart v g hg).head = v := by
  unfold facingDart; rw [mkDart_head]; abel

@[simp] theorem facingDart_dir (v g : Site 2) (hg : unitWt g = 1) :
    (facingDart v g hg).dir = g := by
  unfold facingDart; rw [mkDart_dir]

@[simp] theorem facingDart_tail (v g : Site 2) (hg : unitWt g = 1) :
    (facingDart v g hg).tail = v - g := by
  unfold facingDart; rw [mkDart_tail]



theorem facingDart_isBoundary (K : Set (Site 2)) (v g : Site 2) (hg : unitWt g = 1)
    (htail : v - g ∈ K) (hv : v ∉ K) : IsBoundaryDart K (facingDart v g hg) := by
  refine ⟨?_, ?_⟩
  · rw [facingDart_tail]; exact htail
  · rw [facingDart_head]; exact hv














theorem ifc_arc_to_innerCorner (K : Set (Site 2)) (d : Dart) (v : Site 2) (hv : d.head = v) :
    ∀ k : ℕ, (∀ j < k, v - rot90Fun^[j + 1] d.dir ∈ K) →
      (∀ j < k, IsInnerCorner K ((dartNext K)^[j] d)) := by
  intro k
  induction k with
  | zero => intro _ j hj; omega
  | succ m ih =>
    intro harc j hj
    have harcm : ∀ j' < m, v - rot90Fun^[j' + 1] d.dir ∈ K := fun j' hj' => harc j' (by omega)
    have hcornerm : ∀ j' < m, IsInnerCorner K ((dartNext K)^[j'] d) := ih harcm
    rcases Nat.lt_or_ge j m with hjm | hjm
    · exact hcornerm j hjm
    · have hjeq : j = m := by omega
      subst hjeq
      have hfix := dartNext_iterate_head_fixed K d j hcornerm
      unfold IsInnerCorner
      rw [hfix.1, hfix.2, hv]
      have heq : v + (-rot90Fun (rot90Fun^[j] d.dir)) = v - rot90Fun^[j + 1] d.dir := by
        rw [← Function.iterate_succ_apply' rot90Fun j d.dir]; abel
      rw [heq]; exact harc j (by omega)














theorem ifc_facing_rotateArc_sameOrbit (K : Set (Site 2)) (e d : Dart)
    (hd : IsBoundaryDart K d) (v : Site 2) (hv : d.head = v)
    (hsame : SameOrbit K e d) (k : ℕ)
    (harc : ∀ j < k, v - rot90Fun^[j + 1] d.dir ∈ K) :
    ∃ d' : Dart, IsBoundaryDart K d' ∧ d'.head = v ∧ d'.dir = rot90Fun^[k] d.dir ∧
      SameOrbit K e d' := by
  have hcorner : ∀ j < k, IsInnerCorner K ((dartNext K)^[j] d) := ifc_arc_to_innerCorner K d v hv k harc
  have hfix := dartNext_iterate_isBoundary_head_fixed K d hd k hcorner
  refine ⟨(dartNext K)^[k] d, hfix.1, by rw [hfix.2.1, hv], hfix.2.2, ?_⟩
  obtain ⟨n, hn⟩ := hsame
  exact ⟨k + n, by rw [Function.iterate_add_apply, hn]⟩







theorem ifc_orbitVertexSaturate_contiguous (K : Set (Site 2)) (e d : Dart)
    (hd : IsBoundaryDart K d) (v : Site 2) (hv : d.head = v)
    (hsame : SameOrbit K e d) (k : ℕ)
    (harc : ∀ j < k, v - rot90Fun^[j + 1] d.dir ∈ K)
    (d' : Dart) (_hd' : IsBoundaryDart K d') (hv' : d'.head = v)
    (hdir' : d'.dir = rot90Fun^[k] d.dir) :
    SameOrbit K e d' := by
  obtain ⟨d'', _, hh'', hdd'', hsame''⟩ := ifc_facing_rotateArc_sameOrbit K e d hd v hv hsame k harc
  have hdeq : d'' = d' := dart_eq_of_head_dir (by rw [hh'', hv']) (by rw [hdd'', hdir'])
  rwa [hdeq] at hsame''











theorem ifc_dartNext_singleton (c : Site 2) (e : Dart)
    (he : IsBoundaryDart ({c} : Set (Site 2)) e) :
    (dartNext ({c} : Set (Site 2)) e).tail = c ∧
      (dartNext ({c} : Set (Site 2)) e).dir = -rot90Fun e.dir := by
  have htail : e.tail = c := he.1
  have hA : e.head + (-rot90Fun e.dir) ∉ ({c} : Set (Site 2)) := by
    simp only [Set.mem_singleton_iff]
    intro h
    have key : e.dir = rot90Fun e.dir := by
      have h1 : e.head - e.tail = rot90Fun e.dir := by rw [htail, ← h]; abel
      rw [Dart.dir_def]; exact h1
    exact rot90Fun_dartDir_ne_dartDir e key.symm
  have hB : e.tail + (-rot90Fun e.dir) ∉ ({c} : Set (Site 2)) := by
    simp only [Set.mem_singleton_iff, htail]
    intro h
    have hz : (-rot90Fun e.dir : Site 2) = 0 := by
      exact add_left_cancel (a := c) (b := -rot90Fun e.dir) (c := 0) (by rw [add_zero]; exact h)
    exact neg_rot90Fun_dartDir_ne_zero e hz
  exact ⟨by rw [dartNext_left_tail _ e hA hB, htail], by rw [dartNext_left_dir _ e hA hB]⟩



theorem ifc_dartNext_singleton_iterate (c : Site 2) (e : Dart)
    (he : IsBoundaryDart ({c} : Set (Site 2)) e) (n : ℕ) :
    ((dartNext ({c} : Set (Site 2)))^[n] e).tail = c ∧
      ((dartNext ({c} : Set (Site 2)))^[n] e).dir = (fun x => -rot90Fun x)^[n] e.dir := by
  induction n with
  | zero => exact ⟨he.1, rfl⟩
  | succ m ih =>
    have hbd : IsBoundaryDart ({c} : Set (Site 2)) ((dartNext ({c} : Set (Site 2)))^[m] e) :=
      iterate_isBoundaryDart' _ e he m
    rw [Function.iterate_succ_apply']
    have hstep := ifc_dartNext_singleton c _ hbd
    exact ⟨hstep.1, by rw [hstep.2, ih.2, Function.iterate_succ_apply']⟩



theorem ifc_unit_four_cases (g : Site 2) (hg : unitWt g = 1) :
    g = ![1, 0] ∨ g = ![-1, 0] ∨ g = ![0, 1] ∨ g = ![0, -1] := by
  unfold unitWt at hg
  rw [Fin.sum_univ_two] at hg
  have hcase : ((g 0).natAbs = 1 ∧ (g 1).natAbs = 0) ∨ ((g 0).natAbs = 0 ∧ (g 1).natAbs = 1) := by
    omega
  rcases hcase with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hb' : g 1 = 0 := by omega
    rcases Int.natAbs_eq_iff.mp ha with h | h
    · left; funext i; fin_cases i <;> simp_all
    · right; left; funext i; fin_cases i <;> simp_all
  · have ha' : g 0 = 0 := by omega
    rcases Int.natAbs_eq_iff.mp hb with h | h
    · right; right; left; funext i; fin_cases i <;> simp_all
    · right; right; right; funext i; fin_cases i <;> simp_all




theorem ifc_singleton_cover (g0 g1 : Site 2) (h0 : unitWt g0 = 1) (h1 : unitWt g1 = 1) :
    ∃ n : ℕ, (fun x => -rot90Fun x)^[n] g0 = g1 := by
  rcases ifc_unit_four_cases g0 h0 with rfl | rfl | rfl | rfl <;>
  rcases ifc_unit_four_cases g1 h1 with rfl | rfl | rfl | rfl
  · exact ⟨0, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨2, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨3, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨1, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨2, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨0, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨1, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨3, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨1, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨3, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨0, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨2, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨3, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨1, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨2, by funext i; fin_cases i <;> simp [rot90Fun]⟩
  · exact ⟨0, by funext i; fin_cases i <;> simp [rot90Fun]⟩




theorem ifc_singleton_sameOrbit (c : Site 2) (e f : Dart)
    (he : IsBoundaryDart ({c} : Set (Site 2)) e)
    (hf : IsBoundaryDart ({c} : Set (Site 2)) f) :
    SameOrbit ({c} : Set (Site 2)) e f := by
  obtain ⟨n, hn⟩ := ifc_singleton_cover e.dir f.dir (unitWt_dir e) (unitWt_dir f)
  refine ⟨n, ?_⟩
  have hiter := ifc_dartNext_singleton_iterate c e he n
  have htail : ((dartNext ({c} : Set (Site 2)))^[n] e).tail = f.tail := by rw [hiter.1, hf.1]
  have hdir : ((dartNext ({c} : Set (Site 2)))^[n] e).dir = f.dir := by rw [hiter.2, hn]
  exact dart_eq_of_tail_dir htail hdir







theorem ifc_interfaceConnected (c : Site 2) : InterfaceConnected ({c} : Set (Site 2)) := by
  intro e f he hf _hreach
  exact ifc_singleton_sameOrbit c e f he hf

end Lattice

end StatMech
