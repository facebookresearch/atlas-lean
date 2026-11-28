/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

@[expose] public section

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [Preadditive C]

namespace Splitting

theorem projective_X₃ {S : ShortComplex C} (s : S.Splitting) [Projective S.X₂] :
    Projective S.X₃ :=
  Retract.projective ⟨s.s, S.g, s.s_g⟩

theorem injective_X₁ {S : ShortComplex C} (s : S.Splitting) [Injective S.X₂] :
    Injective S.X₁ :=
  Retract.injective ⟨S.f, s.r, s.f_r⟩

end Splitting

namespace ShortExact

variable [Balanced C]

noncomputable def splittingOfIsSplitMono {S : ShortComplex C} (hS : S.ShortExact)
    [IsSplitMono S.f] : S.Splitting :=
  Splitting.ofExactOfRetraction S hS.exact (retraction S.f) (IsSplitMono.id S.f) hS.epi_g

noncomputable def splittingOfIsSplitEpi {S : ShortComplex C} (hS : S.ShortExact)
    [IsSplitEpi S.g] : S.Splitting :=
  Splitting.ofExactOfSection S hS.exact (section_ S.g) (IsSplitEpi.id S.g) hS.mono_f

theorem projective_X₃ {S : ShortComplex C} (hS : S.ShortExact) [IsSplitMono S.f]
    [Projective S.X₂] : Projective S.X₃ :=
  Splitting.projective_X₃ (splittingOfIsSplitMono hS)

theorem injective_X₁ {S : ShortComplex C} (hS : S.ShortExact) [IsSplitEpi S.g]
    [Injective S.X₂] : Injective S.X₁ :=
  Splitting.injective_X₁ (splittingOfIsSplitEpi hS)

end ShortExact

end CategoryTheory.ShortComplex
