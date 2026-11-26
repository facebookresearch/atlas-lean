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

Let P be preadditive, A abelian, and i:P→A additive and fully faithful, with independent
category universes. A bounded-above cochain complex whose image terms i(K_n) are projective has
K-projective image in A.

For two such complexes K,L with independent upper bounds, a map f:K→L has quasi-isomorphic image
if and only if f is a homotopy equivalence in P. Full faithfulness reflects the isomorphism in
the homotopy category from the projective image.

From an ambient quasi-isomorphism one obtains an inverse g:L→K with f≫g homotopic to id_K and
g≫f homotopic to id_L. The constructed equivalence has forward map equal to the specified f.
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

/-- Let P be preadditive and A abelian in independent category universes, and i:P→A additive and
faithful. For K a cochain complex indexed by ℤ, assume K_n is zero for n>d and every i(K_n) is
projective. The mapped complex i(K) is K-projective: every map from it to an acyclic cochain
complex in A is null-homotopic. -/
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

/-- Let P be preadditive and A abelian, in independent object/morphism universes (uP,vP),(uA,vA),
and i:P→A an additive fully faithful functor. Let K,L be ℤ-indexed cochain complexes in P, zero
above independent bounds dK,dL, and suppose i(K_n),i(L_n) are projective in A for every n∈ℤ. For
f:K→L, the map i(f) is a quasi-isomorphism in A if and only if f is a homotopy equivalence in P.
Projectivity concerns the image terms, and no homology assumption on P is needed. -/
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

/-- Let P be preadditive and A abelian, in independent object/morphism universes (uP,vP),(uA,vA),
and i:P→A an additive fully faithful functor. Let K,L be ℤ-indexed cochain complexes in P, zero
above independent bounds dK,dL, and suppose i(K_n),i(L_n) are projective in A for every n∈ℤ. If
i(f) is a quasi-isomorphism for f:K→L, construct a homotopy equivalence K≃L whose forward map is
f. It has an inverse g:L→K and homotopies f≫g∼id_K, g≫f∼id_L. -/
def projectiveImageHomotopyEquiv
    (K L : CochainComplex P ℤ) (dK dL : ℤ) [K.IsStrictlyLE dK] [L.IsStrictlyLE dL]
    (hprojK : ∀ n : ℤ, Projective (i.obj (K.X n)))
    (hprojL : ∀ n : ℤ, Projective (i.obj (L.X n))) (f : K ⟶ L)
    (hf : QuasiIso ((i.mapHomologicalComplex (.up ℤ)).map f)) : HomotopyEquiv K L :=
  let h := (quasiIso_mapHomologicalComplex_iff_of_projective
    i K L dK dL hprojK hprojL f).1 hf
  let e : HomotopyEquiv K L := Classical.choose h
  e.copy (Homotopy.ofEq (Classical.choose_spec h))

/-- Let P be preadditive and A abelian, in independent object/morphism universes (uP,vP),(uA,vA),
and i:P→A an additive fully faithful functor. Let K,L be ℤ-indexed cochain complexes in P, zero
above independent bounds dK,dL, and suppose i(K_n),i(L_n) are projective in A for every n∈ℤ. For
f:K→L with i(f) quasi-isomorphic, the forward morphism of the constructed source homotopy
equivalence equals f itself. -/
theorem projectiveImageHomotopyEquiv_hom
    (K L : CochainComplex P ℤ) (dK dL : ℤ) [K.IsStrictlyLE dK] [L.IsStrictlyLE dL]
    (hprojK : ∀ n : ℤ, Projective (i.obj (K.X n)))
    (hprojL : ∀ n : ℤ, Projective (i.obj (L.X n))) (f : K ⟶ L)
    (hf : QuasiIso ((i.mapHomologicalComplex (.up ℤ)).map f)) :
    (projectiveImageHomotopyEquiv i K L dK dL hprojK hprojL f hf).hom = f :=
  rfl

/-- Let P be preadditive and A abelian, in independent object/morphism universes (uP,vP),(uA,vA),
and i:P→A an additive fully faithful functor. Let K,L be ℤ-indexed cochain complexes in P, zero
above independent bounds dK,dL, and suppose i(K_n),i(L_n) are projective in A for every n∈ℤ. For
f:K→L with i(f) a quasi-isomorphism, let g be the inverse of its constructed source homotopy
equivalence. There is a homotopy from f≫g:K→K to id_K. -/
def projectiveImageHomInvHomotopy
    (K L : CochainComplex P ℤ) (dK dL : ℤ) [K.IsStrictlyLE dK] [L.IsStrictlyLE dL]
    (hprojK : ∀ n : ℤ, Projective (i.obj (K.X n)))
    (hprojL : ∀ n : ℤ, Projective (i.obj (L.X n))) (f : K ⟶ L)
    (hf : QuasiIso ((i.mapHomologicalComplex (.up ℤ)).map f)) :
    Homotopy (f ≫ (projectiveImageHomotopyEquiv i K L dK dL hprojK hprojL f hf).inv)
      (𝟙 K) :=
  (projectiveImageHomotopyEquiv i K L dK dL hprojK hprojL f hf).homotopyHomInvId

/-- Let P be preadditive and A abelian, in independent object/morphism universes (uP,vP),(uA,vA),
and i:P→A an additive fully faithful functor. Let K,L be ℤ-indexed cochain complexes in P, zero
above independent bounds dK,dL, and suppose i(K_n),i(L_n) are projective in A for every n∈ℤ. For
f:K→L with i(f) quasi-isomorphic and g the constructed inverse, there is a homotopy from g≫f:L→L
to id_L. -/
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
