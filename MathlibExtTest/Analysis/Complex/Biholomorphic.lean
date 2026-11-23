/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Babak Modami
-/
module

public import MathlibExt.Analysis.Complex.Biholomorphic
public import Mathlib.Analysis.Calculus.FDeriv.Basic

@[expose] public section

namespace MathlibExtTest.Analysis.Complex.Biholomorphic

open MetaMathlibExt

-- Analysis 418: Biholomorphic map between domains

lemma I_biholomorphic : IsBiholomorphicOn id (Set.univ : Set ℂ) Set.univ := by
  refine ⟨isOpen_univ, isOpen_univ, differentiableOn_id, ?_, ?_, ?_⟩
  · exact Set.injOn_id _
  · exact Set.image_id _
  · exact ⟨id, differentiableOn_id, Set.bijOn_id _, fun _ _ => rfl, fun _ _ => rfl⟩

end MathlibExtTest.Analysis.Complex.Biholomorphic

end
