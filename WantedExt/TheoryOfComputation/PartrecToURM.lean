/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Decidability.URMBridge

@[expose] public section

set_option autoImplicit false

namespace Cslib.PartrecToURMWanted

/-- **Every partial recursive function is URM-computable**: the converse of
`Cslib.URM.partrec_of_computable`, by compiling `Nat.Partrec.Code` to URM
programs. Source: Soare, *Recursively Enumerable Sets and Degrees*, Ch. I,
Theorem 2.3 (equivalence of URM machines and partial recursive functions);
Shepherdson–Sturgis, "Computability of recursive functions",
*Journal of the ACM* 10 (1963), 217–255. -/
theorem_wanted partrec_to_urm : ∀ {f : ℕ →. ℕ}, Partrec f →
  Cslib.URM.Computable 1 (fun inputs ↦ f (inputs 0))

end Cslib.PartrecToURMWanted
