/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import MathlibExt.Algebra.Homology.Contractible

/-!
# Lifting null-homotopic maps

A null-homotopic map from a complex of projective objects lifts through
every epimorphism of complexes. Dually, a null-homotopic map into a complex
of injective objects extends across every monomorphism of complexes.
The lifted and extended maps are null-homotopic.

An identity contraction therefore makes a complex of projective objects
projective, and a complex of injective objects injective. All constructions
use the given complex shape.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} {c : ComplexShape ι}

namespace Homotopy

private lemma nullHomotopicMap'_hom_eq
    {P Q : HomologicalComplex C c} {f : P ⟶ Q} (h : Homotopy f 0) :
    nullHomotopicMap' (C := P) (D := Q) (fun i j _ => h.hom i j) = f := by
  classical
  have hs : (fun i j => dite (c.Rel j i) (fun _ => h.hom i j) (fun _ => 0)) =
      h.hom := by
    funext i j
    by_cases hij : c.Rel j i
    · simp only [dif_pos hij]
    · rw [dif_neg hij, h.zero i j hij]
  rw [nullHomotopicMap', hs]
  apply HomologicalComplex.hom_ext
  intro i
  change dNext i h.hom + prevD i h.hom = f.f i
  simpa only [HomologicalComplex.zero_f_apply, add_zero] using (h.comm i).symm

/-- Lift a null-homotopic map through an epimorphism using projective source terms. -/
def projectiveLift {P X Y : HomologicalComplex C c} {f : P ⟶ Y}
    [∀ i, Projective (P.X i)] (h : Homotopy f 0) (e : X ⟶ Y) [Epi e] : P ⟶ X :=
  nullHomotopicMap' (C := P) (D := X)
    (fun i j _ => Projective.factorThru (h.hom i j) (e.f j))

/-- The lifted map composes with the epimorphism to the prescribed map. -/
@[reassoc]
theorem projectiveLift_comp {P X Y : HomologicalComplex C c} {f : P ⟶ Y}
    [∀ i, Projective (P.X i)] (h : Homotopy f 0) (e : X ⟶ Y) [Epi e] :
    projectiveLift h e ≫ e = f := by
  rw [projectiveLift, nullHomotopicMap'_comp]
  simpa only [Projective.factorThru_comp] using nullHomotopicMap'_hom_eq h

/-- The lift carries the null homotopy supplied by its extended components. -/
def projectiveLiftNullHomotopy {P X Y : HomologicalComplex C c} {f : P ⟶ Y}
    [∀ i, Projective (P.X i)] (h : Homotopy f 0) (e : X ⟶ Y) [Epi e] :
    Homotopy (projectiveLift h e) 0 :=
  nullHomotopy' (C := P) (D := X)
    (fun i j _ => Projective.factorThru (h.hom i j) (e.f j))

/-- Extend a null-homotopic map across a monomorphism using injective target terms. -/
def injectiveExtension {X Y I : HomologicalComplex C c} {f : X ⟶ I}
    [∀ i, Injective (I.X i)] (h : Homotopy f 0) (m : X ⟶ Y) [Mono m] : Y ⟶ I :=
  nullHomotopicMap' (C := Y) (D := I)
    (fun i j _ => Injective.factorThru (h.hom i j) (m.f i))

/-- The extension restricts along the monomorphism to the prescribed map. -/
@[reassoc]
theorem comp_injectiveExtension {X Y I : HomologicalComplex C c} {f : X ⟶ I}
    [∀ i, Injective (I.X i)] (h : Homotopy f 0) (m : X ⟶ Y) [Mono m] :
    m ≫ injectiveExtension h m = f := by
  rw [injectiveExtension, comp_nullHomotopicMap']
  simpa only [Injective.comp_factorThru] using nullHomotopicMap'_hom_eq h

/-- The extension carries the null homotopy supplied by its extended components. -/
def injectiveExtensionNullHomotopy {X Y I : HomologicalComplex C c} {f : X ⟶ I}
    [∀ i, Injective (I.X i)] (h : Homotopy f 0) (m : X ⟶ Y) [Mono m] :
    Homotopy (injectiveExtension h m) 0 :=
  nullHomotopy' (C := Y) (D := I)
    (fun i j _ => Injective.factorThru (h.hom i j) (m.f i))

end Homotopy

namespace HomologicalComplex

/-- A complex with projective terms and an identity contraction is projective. -/
theorem projective_of_id_homotopic_zero {P : HomologicalComplex C c}
    [∀ i, Projective (P.X i)] (h : Homotopy (𝟙 P) 0) : Projective P where
  factors f e he := by
    letI : Epi e := he
    let hf : Homotopy f 0 :=
      (Homotopy.ofEq (by simp)).trans
        ((h.compRight f).trans (Homotopy.ofEq (by simp)))
    exact ⟨hf.projectiveLift e, hf.projectiveLift_comp e⟩

/-- A complex with injective terms and an identity contraction is injective. -/
theorem injective_of_id_homotopic_zero {I : HomologicalComplex C c}
    [∀ i, Injective (I.X i)] (h : Homotopy (𝟙 I) 0) : Injective I where
  factors g m hm := by
    letI : Mono m := hm
    let hg : Homotopy g 0 :=
      (Homotopy.ofEq (by simp)).trans
        ((h.compLeft g).trans (Homotopy.ofEq (by simp)))
    exact ⟨hg.injectiveExtension m, hg.comp_injectiveExtension m⟩

/-- A contractible complex of projective objects is projective. -/
theorem Contractible.projective {P : HomologicalComplex C c}
    [∀ i, Projective (P.X i)] (h : P.Contractible) : Projective P :=
  projective_of_id_homotopic_zero h.some

/-- A contractible complex of injective objects is injective. -/
theorem Contractible.injective {I : HomologicalComplex C c}
    [∀ i, Injective (I.X i)] (h : I.Contractible) : Injective I :=
  injective_of_id_homotopic_zero h.some

end HomologicalComplex
