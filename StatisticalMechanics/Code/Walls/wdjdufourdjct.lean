/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartOrbit
import Code.Walls.welenterleave

open Finset Set SimpleGraph
open scoped BigOperators

namespace StatMech

namespace Lattice

open StatMech.Walls








structure wdj_Hypermap where
  
  D : Type
  
  [finD : Fintype D]
  
  [decD : DecidableEq D]
  
  α₀ : Equiv.Perm D
  
  α₁ : Equiv.Perm D

attribute [instance] wdj_Hypermap.finD wdj_Hypermap.decD

namespace wdj_Hypermap

variable (M : wdj_Hypermap)



def φ : Equiv.Perm M.D := M.α₁⁻¹ * M.α₀⁻¹

end wdj_Hypermap













structure wdj_HypermapCounts where
  
  nd : ℤ
  
  ne : ℤ
  
  nv : ℤ
  
  nf : ℤ
  
  nc : ℤ

namespace wdj_HypermapCounts

variable (K : wdj_HypermapCounts)


def wdj_ec : ℤ := K.nv + K.ne + K.nf - K.nd



def wdj_genus : ℤ := K.nc - K.wdj_ec / 2


def wdj_planar : Prop := K.wdj_genus = 0

end wdj_HypermapCounts






def wdj_dufourdFig1 : wdj_HypermapCounts := ⟨15, 7, 6, 6, 3⟩

theorem wdj_dufourdFig1_chi : wdj_dufourdFig1.wdj_ec = 4 := by decide
theorem wdj_dufourdFig1_genus : wdj_dufourdFig1.wdj_genus = 1 := by decide
theorem wdj_dufourdFig1_not_planar : ¬ wdj_dufourdFig1.wdj_planar := by
  unfold wdj_HypermapCounts.wdj_planar; decide





def wdj_sphereExample : wdj_HypermapCounts := ⟨4, 2, 2, 2, 1⟩

theorem wdj_sphereExample_planar : wdj_sphereExample.wdj_planar := by
  unfold wdj_HypermapCounts.wdj_planar; decide
theorem wdj_sphereExample_eulerFormula : wdj_sphereExample.wdj_ec = 2 := by decide
theorem wdj_sphereExample_euler_eq_nc :
    wdj_sphereExample.wdj_ec / 2 = wdj_sphereExample.nc := by decide












def wdj_JordanIncrement (before after : wdj_HypermapCounts) : Prop :=
  after.nc = before.nc + 1





theorem wdj_JordanIncrement_witness :
    wdj_JordanIncrement ⟨15, 7, 6, 6, 3⟩ ⟨15, 7, 7, 5, 4⟩ := by
  unfold wdj_JordanIncrement; decide




theorem wdj_JordanIncrement_iff_nc (before after : wdj_HypermapCounts) :
    wdj_JordanIncrement before after ↔ after.nc = before.nc + 1 := Iff.rfl










def wdj_revPerm : Equiv.Perm Dart where
  toFun := Dart.rev
  invFun := Dart.rev
  left_inv := Dart.rev_rev
  right_inv := Dart.rev_rev

@[simp] theorem wdj_revPerm_apply (d : Dart) : wdj_revPerm d = d.rev := rfl




theorem wdj_revPerm_involutive : wdj_revPerm * wdj_revPerm = 1 := by
  refine Equiv.ext (fun d => ?_)
  simp only [Equiv.Perm.mul_apply, wdj_revPerm_apply, Dart.rev_rev, Equiv.Perm.one_apply]





theorem wdj_dartNext_injective (K : Set (Site 2)) :
    Function.Injective (dartNextSub K) :=
  dartNextSub_injective K





theorem wdj_winding_is_combinatorial_map (K : Set (Site 2)) :
    (wdj_revPerm * wdj_revPerm = 1) ∧ Function.Injective (dartNextSub K) :=
  ⟨wdj_revPerm_involutive, wdj_dartNext_injective K⟩














theorem wdj_ec_shape (K : wdj_HypermapCounts) :
    K.wdj_ec = K.nv + K.ne + K.nf - K.nd := rfl




























theorem wdj_orientationConsistent_beyond_increment :
    ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a),
      ¬ wel_OrientationConsistent (![1, 1] : Site 2) Vc :=
  ⟨_, wnu_doubleSquare, wel_doubleSquare_not_orientationConsistent⟩






theorem wdj_windingWall_residue_is_orientation
    (hOriented : ∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a),
      wel_OrientationConsistent (![1, 1] : Site 2) Vc →
        wos_SignsAlternateInColumnOrder (![1, 1] : Site 2) Vc)
    {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (h : wel_OrientationConsistent (![1, 1] : Site 2) Vc) :
    wos_SignsAlternateInColumnOrder (![1, 1] : Site 2) Vc :=
  hOriented a Vc h

end Lattice

end StatMech
