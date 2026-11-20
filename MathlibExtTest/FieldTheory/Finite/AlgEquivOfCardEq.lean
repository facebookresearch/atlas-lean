/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Finite.AlgEquivOfCardEq

/-! # Consumers for `FiniteField.nonempty_algEquiv_of_card_eq` -/

namespace FiniteFieldAlgEquivOfCardEqTest

/-- The exact source statement (which fixed universe 0), with no added
hypothesis. -/
public theorem exactSource (K : Type) [Field K] (L₁ : Type) [Field L₁]
    [Algebra K L₁] [Finite L₁] (L₂ : Type) [Field L₂] [Algebra K L₂]
    [Finite L₂] (h : Nat.card L₁ = Nat.card L₂) :
    Nonempty (L₁ ≃ₐ[K] L₂) :=
  FiniteField.nonempty_algEquiv_of_card_eq K L₁ L₂ h

/-- Higher-universe consumer: the theorem is not restricted to universe
0. -/
public example (K : Type 1) [Field K] (L₁ L₂ : Type 2) [Field L₁]
    [Field L₂] [Algebra K L₁] [Algebra K L₂] [Finite L₁] [Finite L₂]
    (h : Nat.card L₁ = Nat.card L₂) : Nonempty (L₁ ≃ₐ[K] L₂) :=
  FiniteField.nonempty_algEquiv_of_card_eq K L₁ L₂ h

/-- A finite field is isomorphic to itself over any subfield. -/
public example (K L : Type) [Field K] [Field L] [Algebra K L] [Finite L] :
    Nonempty (L ≃ₐ[K] L) :=
  FiniteField.nonempty_algEquiv_of_card_eq K L L rfl

end FiniteFieldAlgEquivOfCardEqTest
