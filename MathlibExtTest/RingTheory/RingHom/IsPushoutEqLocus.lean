/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.RingHom.IsPushoutEqLocus

@[expose] public section

open CategoryTheory

universe u

-- `exactSource` consumer with the original binders.
example {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra C A]
    (s t : A →+* B)
    (hs : letI := s.toAlgebra; Module.Finite A B)
    (hs' : letI := s.toAlgebra; Module.Projective A B)
    (ht : letI := t.toAlgebra; Module.Finite A B)
    (ht' : letI := t.toAlgebra; Module.Projective A B)
    (hgen : s.range ⊔ t.range = ⊤)
    (hequiv : ∀ (T : Type u) [CommRing T],
      _root_.Equivalence fun x y : A →+* T => ∃ φ : B →+* T, φ.comp s = x ∧ φ.comp t = y)
    (hinj : Function.Injective (algebraMap C A))
    (hinv : ∀ a : A, s a = t a ↔ a ∈ Set.range (algebraMap C A)) :
    Module.Finite C A ∧ Module.Projective C A ∧ Module.FaithfullyFlat C A ∧
      IsPushout (CommRingCat.ofHom (algebraMap C A)) (CommRingCat.ofHom (algebraMap C A))
        (CommRingCat.ofHom s) (CommRingCat.ofHom t) :=
  RingHom.isPushout_eqLocus_of_finiteLocallyFree_equivalenceRelation
    s t hs hs' ht ht' hgen hequiv hinj hinv
