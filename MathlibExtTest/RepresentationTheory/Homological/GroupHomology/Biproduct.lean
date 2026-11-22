/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RepresentationTheory.Homological.GroupHomology.Biproduct

open CategoryTheory Limits groupHomology

universe u

/-- The cyclic group of order two, as a multiplicative group. -/
abbrev C2 : Type := Multiplicative (ZMod 2)

/-- The trivial `ℤ`-linear `C2`-representation on `ℤ`. -/
abbrev Triv : Rep ℤ (C2) := Rep.trivial ℤ (C2) ℤ

/-- The new additivity instance for the chains functor fires. -/
example : (groupHomology.chainsFunctor ℤ (C2)).Additive :=
  inferInstance

/-- The new additivity instance for the homology functor fires. -/
example (n : ℕ) : (groupHomology.functor ℤ (C2) n).Additive :=
  inferInstance

/-- The biproduct isomorphism is an isomorphism at a concrete
representation and degree: round trips are identities. -/
example (n : ℕ) :
    (groupHomology.biprodIso ℤ (C2) Triv Triv n).hom ≫
      (groupHomology.biprodIso ℤ (C2) Triv Triv n).inv =
        𝟙 (groupHomology (Triv ⊞ Triv) n) :=
  Iso.hom_inv_id _

/-- The inverse round trip. -/
example (n : ℕ) :
    (groupHomology.biprodIso ℤ (C2) Triv Triv n).inv ≫
      (groupHomology.biprodIso ℤ (C2) Triv Triv n).hom =
        𝟙 (groupHomology Triv n ⊞ groupHomology Triv n) :=
  Iso.inv_hom_id _

/-- The commutation with the first projection, at a concrete
representation and degree. -/
example (n : ℕ) :
    (groupHomology.biprodIso ℤ (C2) Triv Triv n).hom ≫
        (biprod.fst : groupHomology Triv n ⊞ groupHomology Triv n ⟶
          groupHomology Triv n) =
      groupHomology.map (MonoidHom.id (C2))
        (biprod.fst : Triv ⊞ Triv ⟶ Triv) n :=
  groupHomology.biprodIso_hom_fst ℤ (C2) Triv Triv n

/-- The commutation with the second inclusion, at a concrete
representation and degree. -/
example (n : ℕ) :
    (biprod.inr : groupHomology Triv n ⟶
        groupHomology Triv n ⊞ groupHomology Triv n) ≫
      (groupHomology.biprodIso ℤ (C2) Triv Triv n).inv =
      groupHomology.map (MonoidHom.id (C2))
        (biprod.inr : Triv ⟶ Triv ⊞ Triv) n := by
  rw [groupHomology.biprodIso_inv_inr]
