/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

/-
Portions of this file are adapted from:

`StacksFrontier/RingTheory/TensorProduct/IsBaseChangeSpan.lean` (AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b):
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modifications: module paths and outer namespace are adapted for Atlas; source-only documentation
cross-reference attributes are omitted. All original mathematical proof bodies are retained.
-/

public import Mathlib.RingTheory.IsTensorProduct

namespace MathlibExt.DeRhamSource

open _root_.Algebra

/-!
# A base change is spanned by the image of its source

If `f : M →ₗ[R] N` exhibits `N` as the base change of `M` along `R → S`, then the image of `M`
spans `N` over `S`.

## Main results

* `IsBaseChange.span_range_eq_top`: the image of `M` spans the base change `N` over `S`.
-/

@[expose] public section

namespace IsBaseChange

/-- If `N` is the base change of `M` along `R → S`, the image of `M` spans `N` over `S`. -/
theorem span_range_eq_top {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] {f : M →ₗ[R] N} (hf : IsBaseChange S f) :
    Submodule.span S (Set.range f) = ⊤ :=
  eq_top_iff.2 fun n _ =>
    hf.inductionOn (motive := (· ∈ Submodule.span S (Set.range f))) n
      (fun m => Submodule.subset_span ⟨m, rfl⟩)
      (fun s _ hn => Submodule.smul_mem _ s hn) (fun _ _ => Submodule.add_mem _)

end IsBaseChange

end
end MathlibExt.DeRhamSource
