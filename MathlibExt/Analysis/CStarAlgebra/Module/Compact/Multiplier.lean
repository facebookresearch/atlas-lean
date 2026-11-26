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
# Adjointable operators as multipliers of module compacts

Let `B` be a nonunital complex C-star algebra with star-ordered opposite, and `E` a complete
complex normed right C-star module over `B`. Its compact ideal `K_B(E)` is the operator-norm
closed span of the module rank-one operators inside the adjointable algebra `End_B(E)`.

An adjointable operator `T` defines a double centralizer of `K_B(E)` with left and right actions
`k ↦ T k` and `k ↦ k T`. This gives a unital complex star homomorphism `End_B(E) → M(K_B(E))`.
On rank-one operators, `T θ_(x,y)=θ_(T x,y)` and `θ_(x,y) T=θ_(x,T* y)`. This construction does
not assert surjectivity or a multiplier-algebra equivalence and permits the zero module.
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

/-- **Multiplier action of adjointable module operators.** Let `B` be a nonunital complex C-star
algebra whose opposite has a star-ordered partial order, and let `E` be a complete complex
normed right C-star module over `B`. Write `End_B(E)` for its adjointable endomorphisms and
`K_B(E)` for their norm-closed compact ideal. `compactMultiplierHom : End_B(E) →⋆ₐ[ℂ]
M(K_B(E))` is the unital star homomorphism assigning to `T` the double centralizer `(k ↦ T k,
k ↦ k T)`, with the inherited operator norm on the compact ideal. -/
public def compactMultiplierHom :
    letI : NonUnitalCStarAlgebra (CompactEnd B E) :=
      (compactClosedStarIdeal (B := B) (E := E)).carrierCStarAlgebra;
    End B E →⋆ₐ[ℂ] DoubleCentralizer ℂ (CompactEnd B E) := by
  let I := compactClosedStarIdeal (B := B) (E := E)
  letI : NonUnitalCStarAlgebra I := I.carrierCStarAlgebra
  let e : CompactEnd B E ≃⋆ₐ[ℂ] I := StarAlgEquiv.refl ℂ _
  exact DoubleCentralizer.multiplierExtensionUnital I e

/-- **Left multiplier action on module compacts.** Let `B` be a nonunital complex C-star algebra
whose opposite has a star-ordered partial order, and let `E` be a complete complex normed
right C-star module over `B`. Write `End_B(E)` for its adjointable endomorphisms and `K_B(E)`
for their norm-closed compact ideal. for `T ∈ End_B(E)` and `k ∈ K_B(E)`, the left component
of `compactMultiplierHom T` has underlying adjointable operator `T*k`. -/
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

/-- **Right multiplier action on module compacts.** Let `B` be a nonunital complex C-star algebra
whose opposite has a star-ordered partial order, and let `E` be a complete complex normed
right C-star module over `B`. Write `End_B(E)` for its adjointable endomorphisms and `K_B(E)`
for their norm-closed compact ideal. for `T ∈ End_B(E)` and `k ∈ K_B(E)`, the right component
of `compactMultiplierHom T` has underlying adjointable operator `k*T`. -/
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

/-- **Left multiplier on a module rank-one operator.** Let `B` be a nonunital complex C-star
algebra whose opposite has a star-ordered partial order, and let `E` be a complete complex
normed right C-star module over `B`. Write `End_B(E)` for its adjointable endomorphisms and
`K_B(E)` for their norm-closed compact ideal. for `T ∈ End_B(E)` and `x,y ∈ E`, the left
component sends `θ_(x,y)` to `θ_(T x,y)`, where `θ_(x,y)z=x⟨y,z⟩_B`. -/
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

/-- **Right multiplier on a module rank-one operator.** Let `B` be a nonunital complex C-star
algebra whose opposite has a star-ordered partial order, and let `E` be a complete complex
normed right C-star module over `B`. Write `End_B(E)` for its adjointable endomorphisms and
`K_B(E)` for their norm-closed compact ideal. for `T ∈ End_B(E)` and `x,y ∈ E`, the right
component sends `θ_(x,y)` to `θ_(x,T* y)`, where `θ_(x,y)z=x⟨y,z⟩_B`. -/
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
