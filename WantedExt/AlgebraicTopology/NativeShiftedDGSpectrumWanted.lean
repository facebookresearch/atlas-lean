/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.NativeShiftedDGSpectrumModels

/-!
# Full shifted DG spectrum and mapping comparison construction requests

All levels use native zero-pointed DK(good truncation H[q]); the original
Koszul shifts, Alexander--Whitney maps, circle coefficient and full
homogeneous compositions are retained. These are source construction and
mapping-spectrum proofs, with no tangent/RHom endpoint input.
Sources: HA Construction1.3.1.13; Keller §§1--3; HSS §§2.2/3.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicTopology.NativeShiftedDGSpectrumModels

open _root_.CategoryTheory
open MathlibExt.SpectraSource MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open StableSpectraInfinitySource NativeDerivedSpectrumModels

variable (k : Type) [CommRing k]

def_wanted native_pointed_DK_tensor (p q : ℤ) : DoldKanTensorSource k p q

def_wanted native_cochain_circle_source : CochainCircleSource k

def_wanted native_full_cochain_spectrum_source : CochainSpectrumSource k

theorem_wanted native_cochain_quasi_iso_spectrum_map (T : CochainSpectrumSource k)
    (S : SpectrumInfinitySource) {K L : Cochains k} (f : K ⟶ L) (h : QuasiIso f) :
    IsStableWeak S (T.functor.map f)

def_wanted native_full_DG_shift_mapping {C : Type} [DGCategory k C] (X Y : C) (q : ℕ) :
    DGShiftMappingComparison (k := k) X Y q

end MathlibExt.AlgebraicTopology.NativeShiftedDGSpectrumModels
