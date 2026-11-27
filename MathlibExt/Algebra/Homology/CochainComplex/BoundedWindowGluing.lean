/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedWindowWaldhausen

/-!
# Gluing in a fixed window of bounded cochain complexes

Let `E : Type uE` be a preadditive exact category with morphisms in universe `vE`, a zero
object, and binary biproducts. For integers `a, b`, let `Window E a b` consist of cochain
complexes whose terms are zero outside `[a,b]`. Its cofibrations are degreewise admissible
monomorphisms and its weak equivalences are isomorphisms. The gluing axiom holds: a map of
pushout squares along cofibrations that is an isomorphism at the three input objects induces
an isomorphism at the pushout objects.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen

namespace CochainComplex.Bounded

variable (E : Type uE) [Category.{vE} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
variable (a b : ℤ)

/-- Let `E : Type uE` be a preadditive exact category with a zero object, binary biproducts, and
morphisms in universe `vE`. For any `a, b : ℤ`, equip `Window E a b` with degreewise
admissible monomorphisms as cofibrations and isomorphisms as weak equivalences. This structure
satisfies `WaldhausenGluingAxiom`: in a morphism of pushout squares along cofibrations, weak
equivalences on the three input objects induce a weak equivalence on the pushout objects. -/
theorem windowGluing :
    letI := windowWaldhausenCategory E a b
    WaldhausenGluingAxiom (C := Window E a b) := by
  let _ := windowWaldhausenCategory E a b
  let _ := isoWaldhausenCategory E
  let F := windowι E a b
  let hF := windowι_isWaldhausenExact E a b
  constructor
  intro X Y Z P X' Y' Z' P' i f inY inZ i' f' inY' inZ'
    hP hP' x y z p hi hi' wi wf wY wZ hx hy hz
  have hp : IsWeakEquivalence (F.map p) := (isoWaldhausen_gluing E).gluing
    (hF.map_pushout i f inZ inY hi hP.flip).flip
    (hF.map_pushout i' f' inZ' inY' hi' hP'.flip).flip
    (F.map x) (F.map y) (F.map z) (F.map p)
    (hF.map_cofibration i hi) (hF.map_cofibration i' hi')
    (congrArg (fun t : X ⟶ Y' => t.hom) wi)
    (congrArg (fun t : X ⟶ Z' => t.hom) wf)
    (congrArg (fun t : Y ⟶ P' => t.hom) wY)
    (congrArg (fun t : Z ⟶ P' => t.hom) wZ)
    (hF.map_weakEquivalence x hx) (hF.map_weakEquivalence y hy) (hF.map_weakEquivalence z hz)
  exact (window_isWeakEquivalence_iff E a b p).mpr
    ((ObjectProperty.isIso_hom_iff p).mp ((iso_isWeakEquivalence_iff E p.hom).mp hp))

end CochainComplex.Bounded

end
