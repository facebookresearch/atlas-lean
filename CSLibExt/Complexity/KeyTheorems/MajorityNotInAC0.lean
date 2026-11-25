/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.KeyTheorems.RazborovMajorityNotInAC0ModTwo

/-!
# Majority is not in AC0

The strict majority language has no polynomial-size, constant-depth circuit family over
unbounded fan-in AND, OR and unary NOT. This follows from Razborov's lower bound for the
larger class that also allows modulus-two gates.
-/

namespace MetaMathlibExt.Complexity.KeyTheorems.MajorityNotInAC0

open Cslib.Complexity.Classes

/-- **Majority is not in AC0.** The majority language is not in the class $\mathsf{AC}^0$.

Source: M. Ajtai, "Σ₁¹-formulae on finite structures", Annals
of Pure and Applied Logic 24 (1983), 1-48; J. Håstad, "Almost optimal lower bounds for
small depth circuits" (STOC 1986). -/
public theorem majority_not_in_ac0 :
    majorityDec ∉ AC0 := by
  rintro ⟨d, p, C, hC⟩
  apply Smolensky.razborov_majority_not_in_ac0_mod_two
  refine ⟨d, p, C, fun n => ?_⟩
  obtain ⟨hwell, hfree, hsize, hdepth, heval⟩ := hC n
  refine ⟨hwell, ?_, hsize, hdepth, heval⟩
  intro g hg
  cases g <;> try exact True.intro
  exact (hfree _ hg).elim

end MetaMathlibExt.Complexity.KeyTheorems.MajorityNotInAC0
