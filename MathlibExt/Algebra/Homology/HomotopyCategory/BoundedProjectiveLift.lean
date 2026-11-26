/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Lifts from bounded-above projective cochain complexes

Let A be abelian and K a cochain complex whose terms are projective and which vanishes above an
integer cutoff. Every map K → T lifts through a quasi-isomorphism L → T up to a specified chain
homotopy.

If an additive full faithful functor i : P → A sends the terms of F to projective objects and F
has the same bounded-above condition, a map i(F) → T similarly lifts through a quasi-isomorphism
i(G) → T to a complex map F → G, with the required homotopy in A.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uA vA uP vP

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {K L T : CochainComplex A ℤ}

private theorem exists_liftThroughQuasiIso_of_isKProjective [K.IsKProjective]
    (q : L ⟶ T) (hq : QuasiIso q) (f : K ⟶ T) :
    ∃ g : K ⟶ L, Nonempty (Homotopy (g ≫ q) f) := by
  let _ := HasDerivedCategory.standard A
  let U := HomotopyCategory.quotient A (.up ℤ)
  let V := DerivedCategory.Qh (C := A)
  let _ : IsIso (V.map (U.map q)) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso A) q).2
      ((DerivedCategory.isIso_Q_map_iff_quasiIso A q).2 hq)
  obtain ⟨g, hg⟩ := (IsKProjective.Qh_map_bijective K (U.obj L)).surjective
    (V.map (U.map f) ≫ inv (V.map (U.map q)))
  have hgq : g ≫ U.map q = U.map f := by
    apply (IsKProjective.Qh_map_bijective K (U.obj T)).injective
    change V.map (g ≫ U.map q) = V.map (U.map f)
    rw [V.map_comp, hg, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  obtain ⟨g₀, rfl⟩ := U.map_surjective g
  refine ⟨g₀, ⟨HomotopyCategory.homotopyOfEq (g₀ ≫ q) f ?_⟩⟩
  exact (U.map_comp g₀ q).trans hgq

/-- Let A be an abelian category and K,L,T integer cochain complexes. Assume a cutoff d ∈ ℤ with
Kʲ=0 for all j>d and every Kʲ projective. Let q : L → T be a quasi-isomorphism and f : K → T a
complex map. There exists a complex map g : K → L together with a homotopy q ∘ g ≃ f. -/
theorem exists_boundedProjectiveLift (d : ℤ)
    (hzero : ∀ j : ℤ, d < j → IsZero (K.X j))
    (hproj : ∀ j : ℤ, Projective (K.X j))
    (q : L ⟶ T) (hq : QuasiIso q) (f : K ⟶ T) :
    ∃ g : K ⟶ L, Nonempty (Homotopy (g ≫ q) f) := by
  let _ : K.IsStrictlyLE d := (isStrictlyLE_iff K d).2 hzero
  let _ : ∀ j : ℤ, Projective (K.X j) := hproj
  let _ : K.IsKProjective := isKProjective_of_projective K d
  exact exists_liftThroughQuasiIso_of_isKProjective q hq f

/-- Let A be an abelian category and K,L,T integer cochain complexes. Assume a cutoff d ∈ ℤ with
Kʲ=0 for all j>d and every Kʲ projective. Let q : L → T be a quasi-isomorphism and f : K → T a
complex map. Choose a map g : K → L whose composite with q is homotopic to f. -/
@[no_expose]
def boundedProjectiveLift (d : ℤ)
    (hzero : ∀ j : ℤ, d < j → IsZero (K.X j))
    (hproj : ∀ j : ℤ, Projective (K.X j))
    (q : L ⟶ T) (hq : QuasiIso q) (f : K ⟶ T) : K ⟶ L :=
  Classical.choose (exists_boundedProjectiveLift d hzero hproj q hq f)

/-- Let A be an abelian category and K,L,T integer cochain complexes. Assume a cutoff d ∈ ℤ with
Kʲ=0 for all j>d and every Kʲ projective. Let q : L → T be a quasi-isomorphism and f : K → T a
complex map. For the chosen bounded-projective lift g, there is a specified full chain homotopy
q ∘ g ≃ f. -/
@[no_expose]
def boundedProjectiveLiftHomotopy (d : ℤ)
    (hzero : ∀ j : ℤ, d < j → IsZero (K.X j))
    (hproj : ∀ j : ℤ, Projective (K.X j))
    (q : L ⟶ T) (hq : QuasiIso q) (f : K ⟶ T) :
    Homotopy (boundedProjectiveLift d hzero hproj q hq f ≫ q) f :=
  (Classical.choose_spec (exists_boundedProjectiveLift d hzero hproj q hq f)).some

section Images

variable {P : Type uP} [Category.{vP} P] [Preadditive P]
variable (i : P ⥤ A) [i.Additive] [i.Full] [i.Faithful]
variable {F G : CochainComplex P ℤ}

/-- Let A be abelian, P a preadditive category and i : P → A an additive full faithful functor. Let
F,G be integer cochain complexes in P, with Fʲ=0 for j>d and every i(Fʲ) projective in A. Let q
: i(G) → T be a quasi-isomorphism in A and f : i(F) → T a complex map. There exists a
source-category complex map g : F → G such that q ∘ i(g) is homotopic to f. -/
theorem exists_boundedProjectiveImageLift (d : ℤ)
    (hzero : ∀ j : ℤ, d < j → IsZero (F.X j))
    (hproj : ∀ j : ℤ, Projective (i.obj (F.X j)))
    (q : (i.mapHomologicalComplex (.up ℤ)).obj G ⟶ T) (hq : QuasiIso q)
    (f : (i.mapHomologicalComplex (.up ℤ)).obj F ⟶ T) :
    ∃ g : F ⟶ G, Nonempty (Homotopy ((i.mapHomologicalComplex (.up ℤ)).map g ≫ q) f) := by
  have hzero' : ∀ j : ℤ, d < j →
      IsZero (((i.mapHomologicalComplex (.up ℤ)).obj F).X j) :=
    fun j hj => i.map_isZero (hzero j hj)
  obtain ⟨g', hg'⟩ := exists_boundedProjectiveLift d hzero' hproj q hq f
  obtain ⟨g, rfl⟩ := (i.mapHomologicalComplex (.up ℤ)).map_surjective g'
  exact ⟨g, hg'⟩

/-- Let A be abelian, P a preadditive category and i : P → A an additive full faithful functor. Let
F,G be integer cochain complexes in P, with Fʲ=0 for j>d and every i(Fʲ) projective in A. Let q
: i(G) → T be a quasi-isomorphism in A and f : i(F) → T a complex map. Choose a complex map g :
F → G whose image under i lifts f through q up to homotopy. -/
@[no_expose]
def boundedProjectiveImageLift (d : ℤ)
    (hzero : ∀ j : ℤ, d < j → IsZero (F.X j))
    (hproj : ∀ j : ℤ, Projective (i.obj (F.X j)))
    (q : (i.mapHomologicalComplex (.up ℤ)).obj G ⟶ T) (hq : QuasiIso q)
    (f : (i.mapHomologicalComplex (.up ℤ)).obj F ⟶ T) : F ⟶ G :=
  Classical.choose (exists_boundedProjectiveImageLift i d hzero hproj q hq f)

/-- Let A be abelian, P a preadditive category and i : P → A an additive full faithful functor. Let
F,G be integer cochain complexes in P, with Fʲ=0 for j>d and every i(Fʲ) projective in A. Let q
: i(G) → T be a quasi-isomorphism in A and f : i(F) → T a complex map. The image of the chosen
source lift g satisfies a specified homotopy q ∘ i(g) ≃ f in the cochain complexes over A. -/
@[no_expose]
def boundedProjectiveImageLiftHomotopy (d : ℤ)
    (hzero : ∀ j : ℤ, d < j → IsZero (F.X j))
    (hproj : ∀ j : ℤ, Projective (i.obj (F.X j)))
    (q : (i.mapHomologicalComplex (.up ℤ)).obj G ⟶ T) (hq : QuasiIso q)
    (f : (i.mapHomologicalComplex (.up ℤ)).obj F ⟶ T) :
    Homotopy ((i.mapHomologicalComplex (.up ℤ)).map
      (boundedProjectiveImageLift i d hzero hproj q hq f) ≫ q) f :=
  (Classical.choose_spec (exists_boundedProjectiveImageLift i d hzero hproj q hq f)).some

end Images

end CochainComplex

end
