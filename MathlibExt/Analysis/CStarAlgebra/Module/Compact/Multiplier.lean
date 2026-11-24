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

public import MathlibExt.Analysis.CStarAlgebra.Module.Compact
public import MathlibExt.Analysis.CStarAlgebra.Multiplier.Outer

/-!
# Actual adjointable-module operators acting on their compact ideal

The coefficient is the genuine operator-norm closed compact ideal of E.
Every ambient adjointable endomorphism acts on that ideal through its actual
left/right multiplication. No multiplier equivalence, density, surjectivity,
module model or source theorem output is an input. This is the strict map
needed to state Blackadar13.4.1 and its finite/standard module specializations.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped MultiplierAlgebra

namespace CStarModule.AdjointableOperator

noncomputable section
universe uB uE
variable {B : Type uB} {E : Type uE}
variable [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
variable [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- The actual unital ambient-operator action on its own original compact-operator coefficient ideal. -/
public def compactMultiplierHom :
    letI : NonUnitalCStarAlgebra (CompactEnd B E) :=
      (compactClosedStarIdeal (B := B) (E := E)).carrierCStarAlgebra;
    End B E →⋆ₐ[ℂ] DoubleCentralizer ℂ (CompactEnd B E) := by
  let I := compactClosedStarIdeal (B := B) (E := E)
  letI : NonUnitalCStarAlgebra I := I.carrierCStarAlgebra
  let e : CompactEnd B E ≃⋆ₐ[ℂ] I := StarAlgEquiv.refl ℂ _
  exact DoubleCentralizer.multiplierExtensionUnital I e

/-- Every actual compact coefficient has the original left ambient-operator action. -/
public theorem compactMultiplierHom_fst :
    letI : NonUnitalCStarAlgebra (CompactEnd B E) :=
      (compactClosedStarIdeal (B := B) (E := E)).carrierCStarAlgebra;
    ∀ (T : End B E) (k : CompactEnd B E),
      ((compactMultiplierHom (B := B) (E := E) T).fst k : End B E) = T * (k : End B E) := by
  let I := compactClosedStarIdeal (B := B) (E := E)
  let : NonUnitalCStarAlgebra I := I.carrierCStarAlgebra
  let : NonUnitalCStarAlgebra (CompactEnd B E) :=
    (compactClosedStarIdeal (B := B) (E := E)).carrierCStarAlgebra
  let e : CompactEnd B E ≃⋆ₐ[ℂ] I := StarAlgEquiv.refl ℂ _
  exact fun T k => DoubleCentralizer.multiplierExtension_fst I e T k

/-- Every actual compact coefficient has the original right ambient-operator action. -/
public theorem compactMultiplierHom_snd :
    letI : NonUnitalCStarAlgebra (CompactEnd B E) :=
      (compactClosedStarIdeal (B := B) (E := E)).carrierCStarAlgebra;
    ∀ (T : End B E) (k : CompactEnd B E),
      ((compactMultiplierHom (B := B) (E := E) T).snd k : End B E) = (k : End B E) * T := by
  let I := compactClosedStarIdeal (B := B) (E := E)
  let : NonUnitalCStarAlgebra I := I.carrierCStarAlgebra
  let : NonUnitalCStarAlgebra (CompactEnd B E) :=
    (compactClosedStarIdeal (B := B) (E := E)).carrierCStarAlgebra
  let e : CompactEnd B E ≃⋆ₐ[ℂ] I := StarAlgEquiv.refl ℂ _
  exact fun T k => DoubleCentralizer.multiplierExtension_snd I e T k

/-- The actual source multiplier action on every original module rank-one compact. -/
public theorem compactMultiplierHom_fst_rankOne :
    letI : NonUnitalCStarAlgebra (CompactEnd B E) :=
      (compactClosedStarIdeal (B := B) (E := E)).carrierCStarAlgebra;
    ∀ (T : End B E) (x y : E),
      (compactMultiplierHom (B := B) (E := E) T).fst ⟨rankOne x y, rankOne_mem_compact x y⟩ =
        ⟨rankOne (T x) y, rankOne_mem_compact (T x) y⟩ := by
  let : NonUnitalCStarAlgebra (CompactEnd B E) :=
    (compactClosedStarIdeal (B := B) (E := E)).carrierCStarAlgebra
  exact fun T x y => Subtype.ext
    ((compactMultiplierHom_fst (B := B) (E := E) T
      ⟨rankOne x y, rankOne_mem_compact x y⟩).trans (comp_rankOne T x y))

/-- The actual right action carries the adjoint on the original rank-one source vector. -/
public theorem compactMultiplierHom_snd_rankOne :
    letI : NonUnitalCStarAlgebra (CompactEnd B E) :=
      (compactClosedStarIdeal (B := B) (E := E)).carrierCStarAlgebra;
    ∀ (T : End B E) (x y : E),
      (compactMultiplierHom (B := B) (E := E) T).snd ⟨rankOne x y, rankOne_mem_compact x y⟩ =
        ⟨rankOne x (T.adjointOperator y), rankOne_mem_compact x (T.adjointOperator y)⟩ := by
  let : NonUnitalCStarAlgebra (CompactEnd B E) :=
    (compactClosedStarIdeal (B := B) (E := E)).carrierCStarAlgebra
  exact fun T x y => Subtype.ext
    ((compactMultiplierHom_snd (B := B) (E := E) T
      ⟨rankOne x y, rankOne_mem_compact x y⟩).trans (rankOne_comp x y T))

end

end CStarModule.AdjointableOperator
