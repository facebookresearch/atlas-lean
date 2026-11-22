/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.LinearLogic.CLL.CutElimination

/-! # Canonical pinned API for the upstream CLL cut-elimination port

The algorithm is the attributed PR944 source in `CutElimination` and
`Multicut`. This file only connects its Prop-based fragment to the
pinned `CutFreeProof`, whose predicate is `Proof.cutFree : Bool`.
The list entry point is computable with decidable atom equality. Its proof
terms inherit classical reasoning from the source and Mathlib; computable
here describes the returned data, not an intuitionistic proof claim. The
arbitrary-multiset entry point chooses a list representative and is
explicitly noncomputable; it does not impose decidable equality on callers.
-/

@[expose] public section

namespace Cslib.Logic.CLL

universe u

variable {Atom : Type u} {Γ Δ : Sequent Atom}

/-- Source and pinned cut-free proof bundles contain the same proof values. -/
def CF.Proof.equivCutFreeProof : CF.Proof Γ ≃ CutFreeProof Γ where
  toFun p := ⟨p.val, (Proof.isCutFree_iff_cutFree p.val).mp p.property⟩
  invFun p := ⟨p.val, (Proof.isCutFree_iff_cutFree p.val).mpr p.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Compute a cut-free original CLL proof using an explicit list presentation. -/
def Proof.cut_elim_list [DecidableEq Atom]
    {Γ : List (Proposition Atom)} (p : Proof (Γ : Sequent Atom)) :
    CutFreeProof (Γ : Sequent Atom) :=
  CF.Proof.equivCutFreeProof (Proof.cutElimList p)

/-- Every original CLL proof has a cut-free original proof of the same sequent.
This wrapper uses classical atom equality and a classical list representative. -/
noncomputable def Proof.cut_elim (p : Proof Γ) : CutFreeProof Γ := by
  classical
  exact CF.Proof.equivCutFreeProof (Proof.cutElim p)

/-- Cut admissibility in the existing pinned bundle, with explicit list tails. -/
def CutFreeProof.cutAdmList [DecidableEq Atom] {a : Proposition Atom}
    {Γ Δ : List (Proposition Atom)} (p : CutFreeProof (a ::ₘ Γ))
    (q : CutFreeProof (a⫠ ::ₘ Δ)) :
    CutFreeProof ((Γ : Sequent Atom) + (Δ : Sequent Atom)) :=
  CF.Proof.equivCutFreeProof (Proof.cutAdm
    (CF.Proof.equivCutFreeProof.symm p)
    (CF.Proof.equivCutFreeProof.symm q))

end Cslib.Logic.CLL
