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
public import Mathlib.Algebra.Homology.Homotopy

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

/-- In an abelian category `C`, let `P`, `X`, `Y` be complexes of any fixed
shape, with every term of `P` projective. A specified null homotopy of
`f : P → Y` and an epimorphism of complexes `e : X → Y` determine a
lift `P → X`, constructed from lifts of the homotopy components. -/
def projectiveLift {P X Y : HomologicalComplex C c} {f : P ⟶ Y}
    [∀ i, Projective (P.X i)] (h : Homotopy f 0) (e : X ⟶ Y) [Epi e] : P ⟶ X :=
  nullHomotopicMap' (C := P) (D := X)
    (fun i j _ => Projective.factorThru (h.hom i j) (e.f j))

/-- For complexes `P`, `X`, `Y` of a common shape in an abelian category,
with `P` termwise projective, a null homotopy `h` of `f : P → Y` and
an epimorphism `e : X → Y`, the lift satisfies `projectiveLift(h,e) ≫ e = f`. -/
@[reassoc]
theorem projectiveLift_comp {P X Y : HomologicalComplex C c} {f : P ⟶ Y}
    [∀ i, Projective (P.X i)] (h : Homotopy f 0) (e : X ⟶ Y) [Epi e] :
    projectiveLift h e ≫ e = f := by
  rw [projectiveLift, nullHomotopicMap'_comp]
  simpa only [Projective.factorThru_comp] using nullHomotopicMap'_hom_eq h

/-- For complexes of any fixed shape in an abelian category, if `P` is
termwise projective, `h` is a null homotopy of `f : P → Y`, and `e : X → Y`
is epic, the constructed lift `P → X` has a null homotopy obtained from
the lifted components of `h`. -/
def projectiveLiftNullHomotopy {P X Y : HomologicalComplex C c} {f : P ⟶ Y}
    [∀ i, Projective (P.X i)] (h : Homotopy f 0) (e : X ⟶ Y) [Epi e] :
    Homotopy (projectiveLift h e) 0 :=
  nullHomotopy' (C := P) (D := X)
    (fun i j _ => Projective.factorThru (h.hom i j) (e.f j))

/-- In an abelian category `C`, let `X`, `Y`, `I` be complexes of any fixed
shape, with every term of `I` injective. A specified null homotopy of
`f : X → I` and a monomorphism of complexes `m : X → Y` determine an
extension `Y → I`, constructed from extensions of the homotopy components. -/
def injectiveExtension {X Y I : HomologicalComplex C c} {f : X ⟶ I}
    [∀ i, Injective (I.X i)] (h : Homotopy f 0) (m : X ⟶ Y) [Mono m] : Y ⟶ I :=
  nullHomotopicMap' (C := Y) (D := I)
    (fun i j _ => Injective.factorThru (h.hom i j) (m.f i))

/-- For complexes `X`, `Y`, `I` of a common shape in an abelian category,
with `I` termwise injective, a null homotopy `h` of `f : X → I` and a
monomorphism `m : X → Y`, the extension satisfies
`m ≫ injectiveExtension(h,m) = f`. -/
@[reassoc]
theorem comp_injectiveExtension {X Y I : HomologicalComplex C c} {f : X ⟶ I}
    [∀ i, Injective (I.X i)] (h : Homotopy f 0) (m : X ⟶ Y) [Mono m] :
    m ≫ injectiveExtension h m = f := by
  rw [injectiveExtension, comp_nullHomotopicMap']
  simpa only [Injective.comp_factorThru] using nullHomotopicMap'_hom_eq h

/-- For complexes of any fixed shape in an abelian category, if `I` is
termwise injective, `h` is a null homotopy of `f : X → I`, and `m : X → Y`
is monic, the constructed extension `Y → I` has a null homotopy obtained
from the extended components of `h`. -/
def injectiveExtensionNullHomotopy {X Y I : HomologicalComplex C c} {f : X ⟶ I}
    [∀ i, Injective (I.X i)] (h : Homotopy f 0) (m : X ⟶ Y) [Mono m] :
    Homotopy (injectiveExtension h m) 0 :=
  nullHomotopy' (C := Y) (D := I)
    (fun i j _ => Injective.factorThru (h.hom i j) (m.f i))

end Homotopy

namespace HomologicalComplex

/-- In an abelian category, a complex of any given shape whose terms are
projective and whose identity has a specified null homotopy is projective
as an object of the category of complexes of that shape. -/
theorem projective_of_id_homotopic_zero {P : HomologicalComplex C c}
    [∀ i, Projective (P.X i)] (h : Homotopy (𝟙 P) 0) : Projective P where
  factors f e he := by
    letI : Epi e := he
    let hf : Homotopy f 0 :=
      (Homotopy.ofEq (by simp)).trans
        ((h.compRight f).trans (Homotopy.ofEq (by simp)))
    exact ⟨hf.projectiveLift e, hf.projectiveLift_comp e⟩

/-- In an abelian category, a complex of any given shape whose terms are
injective and whose identity has a specified null homotopy is injective
as an object of the category of complexes of that shape. -/
theorem injective_of_id_homotopic_zero {I : HomologicalComplex C c}
    [∀ i, Injective (I.X i)] (h : Homotopy (𝟙 I) 0) : Injective I where
  factors g m hm := by
    letI : Mono m := hm
    let hg : Homotopy g 0 :=
      (Homotopy.ofEq (by simp)).trans
        ((h.compLeft g).trans (Homotopy.ofEq (by simp)))
    exact ⟨hg.injectiveExtension m, hg.comp_injectiveExtension m⟩

/-- In an abelian category, a contractible complex of any given shape
with projective terms is projective in the category of complexes of that
shape. Contractibility means that its identity is homotopic to zero. -/
theorem Contractible.projective {P : HomologicalComplex C c}
    [∀ i, Projective (P.X i)] (h : Nonempty (Homotopy (𝟙 P) 0)) : Projective P :=
  projective_of_id_homotopic_zero h.some

/-- In an abelian category, a contractible complex of any given shape
with injective terms is injective in the category of complexes of that
shape. Contractibility means that its identity is homotopic to zero. -/
theorem Contractible.injective {I : HomologicalComplex C c}
    [∀ i, Injective (I.X i)] (h : Nonempty (Homotopy (𝟙 I) 0)) : Injective I :=
  injective_of_id_homotopic_zero h.some

end HomologicalComplex
