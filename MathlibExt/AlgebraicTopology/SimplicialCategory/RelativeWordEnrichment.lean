/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordOperators

/-!
# The actual normalized relative-word simplicial enrichment

The original scalar operators make the normalized word carriers into
actual simplicial Hom objects. Original identities and normalized word
composition are genuine simplicial maps and satisfy all enriched laws.
The resulting fixed-object enrichment retains every individual original
label; its universal pushout and weak-filtration properties are separate
theorems, not construction inputs.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
open RelativeWords

variable {O : Type u} {C : FixedObjects O}

/-- The actual normalized relative-word Hom simplicial set at the same two original labels. -/
def wordHom (T : Data C) (x y : O) : SSet.{u} where
  obj q := WordAt T q x y
  map f := ↾fun p => operator T f p
  map_id q := by ext p; exact operator_id T q p
  map_comp f g := by ext p; exact (operator_operator T f g p).symm

/-- The actual original identity supplies a genuine simplicial normalized-word identity. -/
def identityHom (T : Data C) (x : O) : 𝟙_ SSet.{u} ⟶ wordHom T x x where
  app q := ↾fun a => oldWord T q ((identityMap C x).app q a)
  naturality q r f := by
    ext a
    change oldWord T r ((identityMap C x).app r ((𝟙_ SSet.{u}).map f a)) =
      operator T f (oldWord T q ((identityMap C x).app q a))
    rw [operator_old]
    exact congrArg (oldWord T r) (congr($((identityMap C x).naturality f) a))

/-- Whole normalized-word concatenation is the actual enriched simplicial composition map. -/
def compositionHom (T : Data C) (x y z : O) : wordHom T x y ⊗ wordHom T y z ⟶ wordHom T x z where
  app q := ↾fun p => compWords T q p.1 p.2
  naturality q r f := by
    ext p
    exact (operator_comp T f p.1 p.2).symm

/-- The actual normalized relative-word enrichment on the unchanged original object labels. -/
@[instance_reducible]
def enrichment (T : Data C) : EnrichedCategory SSet.{u} O where
  Hom := wordHom T
  id := identityHom T
  comp := compositionHom T
  id_comp x y := by
    ext q p
    exact @Word.id_comp O (scalarCategory C q) (newAt T q) x y p
  comp_id x y := by
    ext q p
    exact @Word.comp_id O (scalarCategory C q) (newAt T q) x y p
  assoc w x y z := by
    ext q p
    exact @Word.assoc O (scalarCategory C q) (newAt T q) w x y z p.1 p.2.1 p.2.2

/-- Bundle the actual relative-word enrichment with its same literal original object labels. -/
def object (T : Data C) : FixedObjects O := @FixedObjects.of O (enrichment T)

/-- Each supplied original label is the same individual object of the actual word enrichment. -/
@[simp]
theorem object_vertex (T : Data C) (x : O) : vertex (object T) x = x := rfl

/-- The original fixed-label Hom is literally the actual normalized word simplicial set. -/
theorem object_hom (T : Data C) (x y : O) : hom (object T) x y = wordHom T x y := rfl

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
