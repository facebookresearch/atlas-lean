/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.NaiveFibrations
public import Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty
public import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# Lifting against naive fibrant targets forces monicity

For a monic morphism class with factorization into that class and its right
orthogonal, a terminal-map factorization tests monicity. Its second factor
has the naive fibrant terminal object as codomain, and a lift expresses the
given map as the first factor of a monomorphism.

This is the monicity argument in Joyal's 2008 Lemma 6.5 and the generic
monicity supplement to Cisinski's 2026 Proposition 2.4.30. It requires no
cylinder or model structure and uses the native class of maps with a
specified codomain property.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory.Limits

universe v u

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] [HasTerminal C]

/-- Left lifting against naive fibrations with naive fibrant codomain forces
monicity, using the actual terminal-map factorization. -/
theorem llp_naiveFibrantCodomain_le_monomorphisms (An : MorphismProperty C)
    [HasFactorization An An.naiveFibrations] (hAn : An ≤ monomorphisms C) :
    (An.naiveFibrations ⊓ ofObjectProperty ⊤ An.naiveFibrantObjects).llp ≤
      monomorphisms C := by
  intro X Y f hf
  let d := factorizationData An An.naiveFibrations (terminal.from X)
  have : Mono d.i := hAn d.i d.hi
  have hterminal : An.naiveFibrantObjects (⊤_ C) := by
    change An.rlp (terminal.from (⊤_ C))
    rw [show terminal.from (⊤_ C) = 𝟙 _ from terminal.hom_ext _ _]
    exact An.rlp.id_mem _
  have hq : (An.naiveFibrations ⊓ ofObjectProperty ⊤ An.naiveFibrantObjects) d.p :=
    ⟨d.hp, trivial, hterminal⟩
  have hip : HasLiftingProperty f d.p := hf d.p hq
  have sq : CommSq d.i f d.p (terminal.from Y) := ⟨terminal.hom_ext _ _⟩
  have : sq.HasLift := hip.sq_hasLift sq
  exact mono_of_mono_fac sq.fac_left

end CategoryTheory.MorphismProperty
