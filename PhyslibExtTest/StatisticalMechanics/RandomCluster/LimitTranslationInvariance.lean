/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.LimitTranslationInvariance

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.LimitTranslationInvariance`

In `ℤ²` at `p = 1/2` (`q = 2`):
* `plc_wiredCentredShiftDecay_refl` and `plc_freeCentredShiftDecay_refl`: the shift identities
  hold for an edge set and itself;
* `plc_wiredPlacement_of_decay` and `plc_freePlacement_of_decay` for the identity translation,
  from `plc_wiredCentredShiftDecay_one` / `plc_freeCentredShiftDecay_one`;
* `plc_wiredIV_isTranslationInvariant_of_decay` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.LimitTranslationInvariance

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice

-- The centred-shift identities hold reflexively.
example (t : Finset (Sym2 (boxVerts 2 1))) :
    WiredCentredShiftIdentity (p := 1 / 2) (by norm_num) (by norm_num) 1 t t ∧
      FreeCentredShiftIdentity (p := 1 / 2) (by norm_num) (by norm_num) 1 t t :=
  ⟨plc_wiredCentredShiftDecay_refl _ _ 1 t, plc_freeCentredShiftDecay_refl _ _ 1 t⟩

-- The placement property for the identity translation.
example : med_wiredPlacement (d := 2) (p := 1 / 2) (by norm_num) (by norm_num) 1 ∧
    med_freePlacement (d := 2) (p := 1 / 2) (by norm_num) (by norm_num) 1 :=
  ⟨plc_wiredPlacement_of_decay _ _ 1 (plc_wiredCentredShiftDecay_one _ _),
   plc_freePlacement_of_decay _ _ 1 (plc_freeCentredShiftDecay_one _ _)⟩

-- Given all centred-shift identities, the wired limit is translation invariant.
example := fun hdecay => plc_wiredIV_isTranslationInvariant_of_decay (d := 2) (p := 1 / 2)
  (by norm_num) (by norm_num) hdecay

end PhyslibExtTest.StatisticalMechanics.RandomCluster.LimitTranslationInvariance
