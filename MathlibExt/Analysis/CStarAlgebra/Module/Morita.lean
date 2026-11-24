/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Ideal.Hereditary
public import MathlibExt.Analysis.CStarAlgebra.Module.Compact
public import MathlibExt.Analysis.CStarAlgebra.Module.Support

/-!
# Analytic strong Morita equivalence

Two complex C-star algebras are strongly Morita equivalent when a full right
Hilbert module over the second algebra carries a bijective nonunital star
homomorphism from the first algebra onto its actual compact endomorphism
algebra.  This is an analytic relation and is distinct from ring-theoretic
Morita equivalence.
-/

@[expose] public section

open Set

namespace CStarModule

universe uA uB

/-- Analytic strong Morita equivalence through a full Hilbert module and the
literal compact-operator C-star algebra. -/
def StronglyMoritaEquivalent
    (A : Type uA) (B : Type uB)
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] : Prop :=
  let _ : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let _ : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  ∃ (E : Type (max uA uB)) (hE : NormedAddCommGroup E),
    let _ := hE
    ∃ hES : NormedSpace ℂ E,
    let _ := hES
    ∃ hsmul : SMul Bᵐᵒᵖ E,
    let _ := hsmul
    ∃ hmodule : CStarModule Bᵐᵒᵖ E,
    let _ := hmodule
    ∃ hcomplete : CompleteSpace E,
    let _ := hcomplete
    ∃ α : A →⋆ₙₐ[ℂ] AdjointableOperator.End B E,
      IsFull B E ∧
      ∃ hcompact : ∀ a, α a ∈ AdjointableOperator.compactStarSubalgebra,
        Function.Bijective
          (NonUnitalStarAlgHom.codRestrict α
            AdjointableOperator.compactStarSubalgebra hcompact)

/-- A star subalgebra is full hereditary when it is closed, hereditary in the
shared canonical-order sense, and contained in no proper closed two-sided
ideal. -/
def IsFullHereditarySubalgebra
    {B : Type uB} [NonUnitalCStarAlgebra B]
    (S : NonUnitalStarSubalgebra ℂ B) : Prop :=
  IsClosed (S : Set B) ∧ S.IsHereditary ∧
    ∀ I : ClosedStarIdeal B, (∀ x ∈ S, x ∈ I) → I = ⊤

end CStarModule
