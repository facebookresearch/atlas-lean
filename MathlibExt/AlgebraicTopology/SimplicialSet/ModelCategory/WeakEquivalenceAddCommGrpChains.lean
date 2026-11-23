/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.WeakEquivalenceChains

/-!
# Compatibility import for abelian-group weak-chain invariance

The original `SSet.realizationWeakEquivalences.quasiIso_chainComplexMap_addCommGrp`
name, statement and proof now live once in the canonical weak-chain owner.
The canonical module-coefficient theorem has independent ring and carrier
universes, so its direct integer specialization preserves the entire former
integer-wrapper contract.
-/
