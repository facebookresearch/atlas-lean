/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SubcomplexCountability

/-! # Encodings of the entire union, including an empty labelled family -/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.SubcomplexCountability

/-- The actual total nondegenerate set of the supremum has one Nat encoding. -/
def unionEncoding {Y : SSet.{u}} {I : Type v} [Countable I]
    (V : I → Y.Subcomplex) [∀ i, Countable (V i).toSSet.N] :
    {e : (iSup V).toSSet.N → ℕ // Function.Injective e} := by
  letI := SSet.Subcomplex.countable_N_iSup V
  exact ⟨(Countable.exists_injective_nat _).choose,
    (Countable.exists_injective_nat _).choose_spec⟩

/-- No ambient countability or component hypothesis is needed for an empty family. -/
def emptyEncoding {Y : SSet.{u}} (V : PEmpty.{v + 1} → Y.Subcomplex) :
    {e : (iSup V).toSSet.N → ℕ // Function.Injective e} := by
  letI : ∀ i, Countable (V i).toSSet.N := fun i ↦ PEmpty.elim i
  exact unionEncoding V

end MathlibExtTest.AlgebraicTopology.SimplicialSet.SubcomplexCountability
