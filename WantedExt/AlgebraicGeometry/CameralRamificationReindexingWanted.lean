/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralRamificationReindexing

/-!
# Native all-base cameral symbol and computed-dual comparisons

Comparisons preserve all actual coefficient generators and native tilde
maps, perfect dual pairings and canonical sections. The source maps are
Cartesian cameral arrows, so arbitrary ramified maps are not substituted.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Sections 5.2--5.5.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CameralRamificationReindexingWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages CameralRamificationReindexing ExpansionParameterModels

def_wanted nativeRamificationReindexing (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori) : RamificationReindexing F

def_wanted nativeCameralBaseChange (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    {X X' : Over (Spec (.of ℂ))} (C : Cover F X) (f : X' ⟶ X) : CameralBaseChange F C f

end WantedExt.AlgebraicGeometry.CameralRamificationReindexingWanted
