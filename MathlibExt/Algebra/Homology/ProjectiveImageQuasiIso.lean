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

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Quasi-isomorphisms in a fully faithful projective image

The actual bounded-above image complexes are K-projective when their image
terms are projective. A quasi-isomorphism between these image complexes is
therefore a homotopy equivalence. Full faithfulness of the original resolving
functor reflects the quotient isomorphism to the original complexes.

The constructed source homotopy equivalence retains the specified original
map as its literal forward map. Source and target upper support cutoffs are
independent, and every projectivity hypothesis concerns an actual image term.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uP vP uA vA

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {P : Type uP} [Category.{vP} P] [Preadditive P]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (i : P ⥤ A) [i.Additive] [i.Faithful]

/-- The original image of a bounded-above complex is K-projective when
every actual image term is projective. -/
theorem isKProjective_mapHomologicalComplex_of_projective
    (K : CochainComplex P ℤ) (d : ℤ) [K.IsStrictlyLE d]
    (hproj : ∀ n : ℤ, Projective (i.obj (K.X n))) :
    CochainComplex.IsKProjective ((i.mapHomologicalComplex (.up ℤ)).obj K) := by
  letI : CochainComplex.IsStrictlyLE ((i.mapHomologicalComplex (.up ℤ)).obj K) d :=
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff (K := K) i d).2
      inferInstance
  letI (n : ℤ) : Projective (((i.mapHomologicalComplex (.up ℤ)).obj K).X n) := by
    change Projective (i.obj (K.X n))
    exact hproj n
  exact CochainComplex.isKProjective_of_projective
    ((i.mapHomologicalComplex (.up ℤ)).obj K) d

variable [i.Full]

/-- Ambient quasi-isomorphisms between the actual bounded-above projective
image complexes are exactly homotopy equivalences of the original map. -/
theorem quasiIso_mapHomologicalComplex_iff_of_projective
    (K L : CochainComplex P ℤ) (dK dL : ℤ) [K.IsStrictlyLE dK] [L.IsStrictlyLE dL]
    (hprojK : ∀ n : ℤ, Projective (i.obj (K.X n)))
    (hprojL : ∀ n : ℤ, Projective (i.obj (L.X n))) (f : K ⟶ L) :
    QuasiIso ((i.mapHomologicalComplex (.up ℤ)).map f) ↔
      HomologicalComplex.homotopyEquivalences P (.up ℤ) f := by
  letI := isKProjective_mapHomologicalComplex_of_projective i K dK hprojK
  letI := isKProjective_mapHomologicalComplex_of_projective i L dL hprojL
  constructor
  · intro hf
    have himage : HomologicalComplex.homotopyEquivalences A (.up ℤ)
        ((i.mapHomologicalComplex (.up ℤ)).map f) :=
      (CochainComplex.IsKProjective.quasiIso_iff
        ((i.mapHomologicalComplex (.up ℤ)).map f)).1 hf
    letI : IsIso ((i.mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quotient P (.up ℤ)).map f)) := by
      rw [CategoryTheory.Functor.mapHomotopyCategory_map]
      exact (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences
        ((i.mapHomologicalComplex (.up ℤ)).map f)).2 himage
    have hsource : IsIso ((HomotopyCategory.quotient P (.up ℤ)).map f) :=
      CategoryTheory.isIso_of_reflects_iso
        ((HomotopyCategory.quotient P (.up ℤ)).map f) (i.mapHomotopyCategory (.up ℤ))
    exact (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences f).1 hsource
  · intro hf
    exact _root_.homotopyEquivalences_le_quasiIso A (.up ℤ)
      ((i.mapHomologicalComplex (.up ℤ)).map f)
      (i.homotopyEquivalences_mapHomologicalComplex_map f hf)

/-- Construct an actual source homotopy equivalence from the original
ambient quasi-isomorphism. Its forward map is literally the specified map. -/
def projectiveImageHomotopyEquiv
    (K L : CochainComplex P ℤ) (dK dL : ℤ) [K.IsStrictlyLE dK] [L.IsStrictlyLE dL]
    (hprojK : ∀ n : ℤ, Projective (i.obj (K.X n)))
    (hprojL : ∀ n : ℤ, Projective (i.obj (L.X n))) (f : K ⟶ L)
    (hf : QuasiIso ((i.mapHomologicalComplex (.up ℤ)).map f)) : HomotopyEquiv K L :=
  let h := (quasiIso_mapHomologicalComplex_iff_of_projective
    i K L dK dL hprojK hprojL f).1 hf
  let e : HomotopyEquiv K L := Classical.choose h
  e.copy (Homotopy.ofEq (Classical.choose_spec h))

/-- The actual source equivalence retains the original forward chain map. -/
theorem projectiveImageHomotopyEquiv_hom
    (K L : CochainComplex P ℤ) (dK dL : ℤ) [K.IsStrictlyLE dK] [L.IsStrictlyLE dL]
    (hprojK : ∀ n : ℤ, Projective (i.obj (K.X n)))
    (hprojL : ∀ n : ℤ, Projective (i.obj (L.X n))) (f : K ⟶ L)
    (hf : QuasiIso ((i.mapHomologicalComplex (.up ℤ)).map f)) :
    (projectiveImageHomotopyEquiv i K L dK dL hprojK hprojL f hf).hom = f :=
  rfl

/-- The actual inverse comes with a homotopy from original forward map
followed by inverse to the identity of the unchanged source complex. -/
def projectiveImageHomInvHomotopy
    (K L : CochainComplex P ℤ) (dK dL : ℤ) [K.IsStrictlyLE dK] [L.IsStrictlyLE dL]
    (hprojK : ∀ n : ℤ, Projective (i.obj (K.X n)))
    (hprojL : ∀ n : ℤ, Projective (i.obj (L.X n))) (f : K ⟶ L)
    (hf : QuasiIso ((i.mapHomologicalComplex (.up ℤ)).map f)) :
    Homotopy (f ≫ (projectiveImageHomotopyEquiv i K L dK dL hprojK hprojL f hf).inv)
      (𝟙 K) :=
  (projectiveImageHomotopyEquiv i K L dK dL hprojK hprojL f hf).homotopyHomInvId

/-- The actual inverse comes with a homotopy from inverse followed by the
original forward map to the identity of the unchanged target complex. -/
def projectiveImageInvHomHomotopy
    (K L : CochainComplex P ℤ) (dK dL : ℤ) [K.IsStrictlyLE dK] [L.IsStrictlyLE dL]
    (hprojK : ∀ n : ℤ, Projective (i.obj (K.X n)))
    (hprojL : ∀ n : ℤ, Projective (i.obj (L.X n))) (f : K ⟶ L)
    (hf : QuasiIso ((i.mapHomologicalComplex (.up ℤ)).map f)) :
    Homotopy ((projectiveImageHomotopyEquiv i K L dK dL hprojK hprojL f hf).inv ≫ f)
      (𝟙 L) :=
  (projectiveImageHomotopyEquiv i K L dK dL hprojK hprojL f hf).homotopyInvHomId

end CategoryTheory.Functor

end
