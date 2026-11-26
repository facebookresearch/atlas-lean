/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.Projective.Horseshoe
public import MathlibExt.CategoryTheory.Abelian.Projective.ResolutionComparison

/- Proof implementation note.
# Comparison maps between categorical horseshoe resolutions

Compatible maps on a short exact sequence and on its endpoint projective
resolutions have a comparison of chosen horseshoe resolutions that is lower
triangular in Mathlib's `Biprod.ofComponents` convention: the
`P₁`-to-`P₃'` component vanishes and the `P₃`-to-`P₁'` cross component is
free.  The comparison is returned only under `Nonempty`; no canonical
choice or homotopy uniqueness is asserted here.  Supplied comparisons
nevertheless have strict identity, composition, and transport
operations, with the associated unit, associativity, and transport
coherence laws stated after transport along the corresponding
equalities of maps of short complexes.
-/

/-!
# Comparison morphisms of projective horseshoes

In an abelian category `C`, a map of short exact sequences and maps
between the chosen endpoint projective resolutions extend to a strictly
compatible comparison of horseshoe middle resolutions. In chosen
endpoint biproduct coordinates, its diagonal entries are the endpoint
maps, its `P₁ → P₃′` corner is zero, and its `P₃ → P₁′` corner
is the remaining comparison component.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory.Limits

namespace CategoryTheory.ProjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S S' : ShortComplex C} (hS : S.ShortExact) (hS' : S'.ShortExact)
variable (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃)
variable (P₁' : ProjectiveResolution S'.X₁) (P₃' : ProjectiveResolution S'.X₃)
variable (H : HorseshoeData hS P₁ P₃) (H' : HorseshoeData hS' P₁' P₃')
variable (sH : H.Spec) (sH' : H'.Spec)
variable (φ : S ⟶ S')
variable (u : ProjectiveResolution.Hom P₁ P₁' φ.τ₁)
variable (w : ProjectiveResolution.Hom P₃ P₃' φ.τ₃)

namespace HorseshoeData

/-- In an abelian category `C`, take short exact sequences `S,S′`,
projective endpoint resolutions `P₁,P₃` and `P₁′,P₃′`, and
horseshoe resolutions `H,H′`. A strict comparison over
`φ : S → S′` and endpoint resolution maps `u,w` consists of
a middle chain map commuting with both endpoint maps and the
middle augmentations. -/
structure Hom where
  /-- In an abelian category `C`, take short exact sequences `S,S′`,
projective endpoint resolutions `P₁,P₃` and `P₁′,P₃′`, and
horseshoe resolutions `H,H′`. The middle component
is a chain map `H.middle.complex → H′.middle.complex`, extending
the prescribed endpoint comparisons over `φ`. -/
  hom : H.middle.complex ⟶ H'.middle.complex
  /-- In an abelian category `C`, take short exact sequences `S,S′`,
projective endpoint resolutions `P₁,P₃` and `P₁′,P₃′`, and
horseshoe resolutions `H,H′`. For a comparison `F`
over `φ` with left endpoint map `u`, strict compatibility means
`H.i ≫ F.hom = u.hom ≫ H′.i`. -/
  comm_i : H.i ≫ hom = u.hom ≫ H'.i
  /-- In an abelian category `C`, take short exact sequences `S,S′`,
projective endpoint resolutions `P₁,P₃` and `P₁′,P₃′`, and
horseshoe resolutions `H,H′`. For a comparison `F`
over `φ` with right endpoint map `w`, strict compatibility means
`F.hom ≫ H′.p = H.p ≫ w.hom`. -/
  comm_p : hom ≫ H'.p = H.p ≫ w.hom
  /-- In an abelian category `C`, take short exact sequences `S,S′`,
projective endpoint resolutions `P₁,P₃` and `P₁′,P₃′`, and
horseshoe resolutions `H,H′`. The middle comparison
over `φ` respects augmentations: its composite with the target
augmentation equals the source augmentation followed by the
degree-zero map induced by `φ₂`. -/
  augmentation :
    hom ≫ H'.middle.π =
      H.middle.π ≫ (ChainComplex.single₀ C).map φ.τ₂

namespace Hom

/-- In an abelian category `C`, take short exact sequences `S,S′`,
projective endpoint resolutions `P₁,P₃` and `P₁′,P₃′`, and
horseshoe resolutions `H,H′`. A strict horseshoe
comparison over `φ` defines a projective-resolution morphism
between the middle objects, over `φ₂ : S.X₂ → S′.X₂`. -/
def toProjectiveResolutionHom (F : HorseshoeData.Hom
    (H := H) (H' := H') (φ := φ) (u := u) (w := w)) :
    ProjectiveResolution.Hom H.middle H'.middle φ.τ₂ where
  hom := F.hom
  hom_f_zero_comp_π_f_zero := by
    simpa only [HomologicalComplex.comp_f] using
      HomologicalComplex.congr_hom F.augmentation 0

@[simp]
theorem toProjectiveResolutionHom_hom (F : HorseshoeData.Hom
    (H := H) (H' := H') (φ := φ) (u := u) (w := w)) :
    F.toProjectiveResolutionHom.hom = F.hom :=
  rfl

/-- In an abelian category `C`, take short exact sequences `S,S′`,
projective endpoint resolutions `P₁,P₃` and `P₁′,P₃′`, and
horseshoe resolutions `H,H′`. Two comparisons over
the same sequence map and endpoint maps are equal if their
middle chain maps are equal. -/
@[ext]
theorem ext {F G : HorseshoeData.Hom
    (H := H) (H' := H') (φ := φ) (u := u) (w := w)}
    (h : F.hom = G.hom) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- For horseshoe data `H` over a short exact sequence `S` in an
abelian category `C`, the identity of its middle resolution gives
a strict comparison over `𝟙 S` and the identity endpoint resolution maps. -/
def id {S : ShortComplex C} {hS : S.ShortExact}
    {P₁ : ProjectiveResolution S.X₁} {P₃ : ProjectiveResolution S.X₃}
    (H : HorseshoeData hS P₁ P₃) :
    Hom (H := H) (H' := H) (φ := 𝟙 S)
      (u := ProjectiveResolution.Hom.id P₁)
      (w := ProjectiveResolution.Hom.id P₃) where
  hom := 𝟙 H.middle.complex
  comm_i := by simp
  comm_p := by simp
  augmentation := by simp

@[simp]
theorem id_hom {S : ShortComplex C} {hS : S.ShortExact}
    {P₁ : ProjectiveResolution S.X₁} {P₃ : ProjectiveResolution S.X₃}
    (H : HorseshoeData hS P₁ P₃) :
    (Hom.id H).hom = 𝟙 H.middle.complex :=
  rfl

/-- In an abelian category `C`, strict comparisons between three
horseshoes compose by composing their middle chain maps,
sequence maps, and supplied endpoint projective-resolution maps. -/
def comp {S S' S'' : ShortComplex C} {hS : S.ShortExact}
    {hS' : S'.ShortExact} {hS'' : S''.ShortExact}
    {P₁ : ProjectiveResolution S.X₁} {P₃ : ProjectiveResolution S.X₃}
    {P₁' : ProjectiveResolution S'.X₁} {P₃' : ProjectiveResolution S'.X₃}
    {P₁'' : ProjectiveResolution S''.X₁}
    {P₃'' : ProjectiveResolution S''.X₃}
    {H : HorseshoeData hS P₁ P₃} {H' : HorseshoeData hS' P₁' P₃'}
    {H'' : HorseshoeData hS'' P₁'' P₃''}
    {φ : S ⟶ S'} {φ' : S' ⟶ S''}
    {u : ProjectiveResolution.Hom P₁ P₁' φ.τ₁}
    {u' : ProjectiveResolution.Hom P₁' P₁'' φ'.τ₁}
    {w : ProjectiveResolution.Hom P₃ P₃' φ.τ₃}
    {w' : ProjectiveResolution.Hom P₃' P₃'' φ'.τ₃}
    (F : Hom (H := H) (H' := H') (φ := φ) (u := u) (w := w))
    (G : Hom (H := H') (H' := H'') (φ := φ') (u := u') (w := w')) :
    Hom (H := H) (H' := H'') (φ := φ ≫ φ')
      (u := u.comp u') (w := w.comp w') where
  hom := F.hom ≫ G.hom
  comm_i := by
    simp only [Category.assoc, ProjectiveResolution.Hom.comp_hom]
    rw [reassoc_of% F.comm_i, G.comm_i]
  comm_p := by
    simp only [Category.assoc, ProjectiveResolution.Hom.comp_hom]
    rw [G.comm_p, reassoc_of% F.comm_p]
  augmentation := by
    rw [show (φ ≫ φ').τ₂ = φ.τ₂ ≫ φ'.τ₂ from rfl, Functor.map_comp]
    simp only [Category.assoc]
    rw [G.augmentation, reassoc_of% F.augmentation]

@[simp]
theorem comp_hom {S S' S'' : ShortComplex C} {hS : S.ShortExact}
    {hS' : S'.ShortExact} {hS'' : S''.ShortExact}
    {P₁ : ProjectiveResolution S.X₁} {P₃ : ProjectiveResolution S.X₃}
    {P₁' : ProjectiveResolution S'.X₁} {P₃' : ProjectiveResolution S'.X₃}
    {P₁'' : ProjectiveResolution S''.X₁}
    {P₃'' : ProjectiveResolution S''.X₃}
    {H : HorseshoeData hS P₁ P₃} {H' : HorseshoeData hS' P₁' P₃'}
    {H'' : HorseshoeData hS'' P₁'' P₃''}
    {φ : S ⟶ S'} {φ' : S' ⟶ S''}
    {u : ProjectiveResolution.Hom P₁ P₁' φ.τ₁}
    {u' : ProjectiveResolution.Hom P₁' P₁'' φ'.τ₁}
    {w : ProjectiveResolution.Hom P₃ P₃' φ.τ₃}
    {w' : ProjectiveResolution.Hom P₃' P₃'' φ'.τ₃}
    (F : Hom (H := H) (H' := H') (φ := φ) (u := u) (w := w))
    (G : Hom (H := H') (H' := H'') (φ := φ') (u := u') (w := w')) :
    (F.comp G).hom = F.hom ≫ G.hom :=
  rfl

/-- In an abelian category `C`, take short exact sequences `S,S′`,
projective endpoint resolutions `P₁,P₃` and `P₁′,P₃′`, and
horseshoe resolutions `H,H′`. Identifying equal
sequence maps `φ=φ′` and the corresponding endpoint resolution
maps transports a horseshoe comparison without changing its middle chain map. -/
def cast {S S' : ShortComplex C} {hS : S.ShortExact}
    {hS' : S'.ShortExact}
    {P₁ : ProjectiveResolution S.X₁} {P₃ : ProjectiveResolution S.X₃}
    {P₁' : ProjectiveResolution S'.X₁} {P₃' : ProjectiveResolution S'.X₃}
    {H : HorseshoeData hS P₁ P₃} {H' : HorseshoeData hS' P₁' P₃'}
    {φ φ' : S ⟶ S'}
    {u : ProjectiveResolution.Hom P₁ P₁' φ.τ₁}
    {u' : ProjectiveResolution.Hom P₁ P₁' φ'.τ₁}
    {w : ProjectiveResolution.Hom P₃ P₃' φ.τ₃}
    {w' : ProjectiveResolution.Hom P₃ P₃' φ'.τ₃}
    (F : Hom (H := H) (H' := H') (φ := φ) (u := u) (w := w))
    (hφ : φ = φ')
    (hu : u.cast (congrArg (fun ψ : S ⟶ S' => ψ.τ₁) hφ) = u')
    (hw : w.cast (congrArg (fun ψ : S ⟶ S' => ψ.τ₃) hφ) = w') :
    Hom (H := H) (H' := H') (φ := φ') (u := u') (w := w') where
  hom := F.hom
  comm_i := by
    subst hφ
    subst hu
    simpa only [ProjectiveResolution.Hom.cast_hom] using F.comm_i
  comm_p := by
    subst hφ
    subst hw
    simpa only [ProjectiveResolution.Hom.cast_hom] using F.comm_p
  augmentation := by
    subst hφ
    exact F.augmentation

@[simp]
theorem cast_hom {S S' : ShortComplex C} {hS : S.ShortExact}
    {hS' : S'.ShortExact}
    {P₁ : ProjectiveResolution S.X₁} {P₃ : ProjectiveResolution S.X₃}
    {P₁' : ProjectiveResolution S'.X₁} {P₃' : ProjectiveResolution S'.X₃}
    {H : HorseshoeData hS P₁ P₃} {H' : HorseshoeData hS' P₁' P₃'}
    {φ φ' : S ⟶ S'}
    {u : ProjectiveResolution.Hom P₁ P₁' φ.τ₁}
    {u' : ProjectiveResolution.Hom P₁ P₁' φ'.τ₁}
    {w : ProjectiveResolution.Hom P₃ P₃' φ.τ₃}
    {w' : ProjectiveResolution.Hom P₃ P₃' φ'.τ₃}
    (F : Hom (H := H) (H' := H') (φ := φ) (u := u) (w := w))
    (hφ : φ = φ')
    (hu : u.cast (congrArg (fun ψ : S ⟶ S' => ψ.τ₁) hφ) = u')
    (hw : w.cast (congrArg (fun ψ : S ⟶ S' => ψ.τ₃) hφ) = w') :
    (F.cast hφ hu hw).hom = F.hom :=
  rfl

/-- For horseshoe data in an abelian category `C`, the middle
projective-resolution morphism induced by the identity horseshoe
comparison is the identity of the middle resolution. -/
@[simp]
theorem toProjectiveResolutionHom_id {S : ShortComplex C}
    {hS : S.ShortExact}
    {P₁ : ProjectiveResolution S.X₁} {P₃ : ProjectiveResolution S.X₃}
    (H : HorseshoeData hS P₁ P₃) :
    (Hom.id H).toProjectiveResolutionHom =
      ProjectiveResolution.Hom.id H.middle :=
  ProjectiveResolution.Hom.ext rfl

/-- For composable horseshoe comparisons in an abelian category `C`,
the projective-resolution morphism induced on the middle objects
is the composite of the two induced middle resolution morphisms. -/
@[simp]
theorem toProjectiveResolutionHom_comp {S S' S'' : ShortComplex C}
    {hS : S.ShortExact} {hS' : S'.ShortExact} {hS'' : S''.ShortExact}
    {P₁ : ProjectiveResolution S.X₁} {P₃ : ProjectiveResolution S.X₃}
    {P₁' : ProjectiveResolution S'.X₁} {P₃' : ProjectiveResolution S'.X₃}
    {P₁'' : ProjectiveResolution S''.X₁}
    {P₃'' : ProjectiveResolution S''.X₃}
    {H : HorseshoeData hS P₁ P₃} {H' : HorseshoeData hS' P₁' P₃'}
    {H'' : HorseshoeData hS'' P₁'' P₃''}
    {φ : S ⟶ S'} {φ' : S' ⟶ S''}
    {u : ProjectiveResolution.Hom P₁ P₁' φ.τ₁}
    {u' : ProjectiveResolution.Hom P₁' P₁'' φ'.τ₁}
    {w : ProjectiveResolution.Hom P₃ P₃' φ.τ₃}
    {w' : ProjectiveResolution.Hom P₃' P₃'' φ'.τ₃}
    (F : Hom (H := H) (H' := H') (φ := φ) (u := u) (w := w))
    (G : Hom (H := H') (H' := H'') (φ := φ') (u := u') (w := w')) :
    (F.comp G).toProjectiveResolutionHom =
      F.toProjectiveResolutionHom.comp G.toProjectiveResolutionHom :=
  ProjectiveResolution.Hom.ext rfl

/-- In an abelian category `C`, take short exact sequences `S,S′`,
projective endpoint resolutions `P₁,P₃` and `P₁′,P₃′`, and
horseshoe resolutions `H,H′`. Transport of the
sequence and endpoint maps transports the induced middle
projective-resolution morphism along the equality of the middle sequence component. -/
@[simp]
theorem toProjectiveResolutionHom_cast {S S' : ShortComplex C}
    {hS : S.ShortExact} {hS' : S'.ShortExact}
    {P₁ : ProjectiveResolution S.X₁} {P₃ : ProjectiveResolution S.X₃}
    {P₁' : ProjectiveResolution S'.X₁} {P₃' : ProjectiveResolution S'.X₃}
    {H : HorseshoeData hS P₁ P₃} {H' : HorseshoeData hS' P₁' P₃'}
    {φ φ' : S ⟶ S'}
    {u : ProjectiveResolution.Hom P₁ P₁' φ.τ₁}
    {u' : ProjectiveResolution.Hom P₁ P₁' φ'.τ₁}
    {w : ProjectiveResolution.Hom P₃ P₃' φ.τ₃}
    {w' : ProjectiveResolution.Hom P₃ P₃' φ'.τ₃}
    (F : Hom (H := H) (H' := H') (φ := φ) (u := u) (w := w))
    (hφ : φ = φ')
    (hu : u.cast (congrArg (fun ψ : S ⟶ S' => ψ.τ₁) hφ) = u')
    (hw : w.cast (congrArg (fun ψ : S ⟶ S' => ψ.τ₃) hφ) = w') :
    (F.cast hφ hu hw).toProjectiveResolutionHom =
      F.toProjectiveResolutionHom.cast
        (congrArg (fun ψ : S ⟶ S' => ψ.τ₂) hφ) :=
  ProjectiveResolution.Hom.ext rfl

@[simp]
theorem cast_rfl {S S' : ShortComplex C} {hS : S.ShortExact}
    {hS' : S'.ShortExact}
    {P₁ : ProjectiveResolution S.X₁} {P₃ : ProjectiveResolution S.X₃}
    {P₁' : ProjectiveResolution S'.X₁} {P₃' : ProjectiveResolution S'.X₃}
    {H : HorseshoeData hS P₁ P₃} {H' : HorseshoeData hS' P₁' P₃'}
    {φ : S ⟶ S'}
    {u : ProjectiveResolution.Hom P₁ P₁' φ.τ₁}
    {w : ProjectiveResolution.Hom P₃ P₃' φ.τ₃}
    (F : Hom (H := H) (H' := H') (φ := φ) (u := u) (w := w)) :
    F.cast rfl rfl rfl = F :=
  HorseshoeData.Hom.ext (h := by simp only [cast_hom])

/-- In an abelian category `C`, take short exact sequences `S,S′`,
projective endpoint resolutions `P₁,P₃` and `P₁′,P₃′`, and
horseshoe resolutions `H,H′`. Two successive
identifications of the sequence map and endpoint maps give the
same transported comparison as their composite identifications. -/
theorem cast_cast {S S' : ShortComplex C} {hS : S.ShortExact}
    {hS' : S'.ShortExact}
    {P₁ : ProjectiveResolution S.X₁} {P₃ : ProjectiveResolution S.X₃}
    {P₁' : ProjectiveResolution S'.X₁} {P₃' : ProjectiveResolution S'.X₃}
    {H : HorseshoeData hS P₁ P₃} {H' : HorseshoeData hS' P₁' P₃'}
    {φ φ' φ'' : S ⟶ S'}
    {u : ProjectiveResolution.Hom P₁ P₁' φ.τ₁}
    {u' : ProjectiveResolution.Hom P₁ P₁' φ'.τ₁}
    {u'' : ProjectiveResolution.Hom P₁ P₁' φ''.τ₁}
    {w : ProjectiveResolution.Hom P₃ P₃' φ.τ₃}
    {w' : ProjectiveResolution.Hom P₃ P₃' φ'.τ₃}
    {w'' : ProjectiveResolution.Hom P₃ P₃' φ''.τ₃}
    (F : Hom (H := H) (H' := H') (φ := φ) (u := u) (w := w))
    (h : φ = φ')
    (hu : u.cast (congrArg (fun ψ : S ⟶ S' => ψ.τ₁) h) = u')
    (hw : w.cast (congrArg (fun ψ : S ⟶ S' => ψ.τ₃) h) = w')
    (h' : φ' = φ'')
    (hu' : u'.cast (congrArg (fun ψ : S ⟶ S' => ψ.τ₁) h') = u'')
    (hw' : w'.cast (congrArg (fun ψ : S ⟶ S' => ψ.τ₃) h') = w'')
    (hu'' : u.cast (congrArg (fun ψ : S ⟶ S' => ψ.τ₁) (h.trans h')) = u'')
    (hw'' : w.cast
      (congrArg (fun ψ : S ⟶ S' => ψ.τ₃) (h.trans h')) = w'') :
    (F.cast h hu hw).cast h' hu' hw' = F.cast (h.trans h') hu'' hw'' :=
  HorseshoeData.Hom.ext (h := by simp only [cast_hom])

/-- In an abelian category `C`, take short exact sequences `S,S′`,
projective endpoint resolutions `P₁,P₃` and `P₁′,P₃′`, and
horseshoe resolutions `H,H′`. Composing the source
identity comparison with a comparison `F` gives `F` after the
canonical identifications of the resolved sequence and endpoint maps. -/
theorem id_comp {S S' : ShortComplex C} {hS : S.ShortExact}
    {hS' : S'.ShortExact}
    {P₁ : ProjectiveResolution S.X₁} {P₃ : ProjectiveResolution S.X₃}
    {P₁' : ProjectiveResolution S'.X₁} {P₃' : ProjectiveResolution S'.X₃}
    {H : HorseshoeData hS P₁ P₃} {H' : HorseshoeData hS' P₁' P₃'}
    {φ : S ⟶ S'}
    {u : ProjectiveResolution.Hom P₁ P₁' φ.τ₁}
    {w : ProjectiveResolution.Hom P₃ P₃' φ.τ₃}
    (F : Hom (H := H) (H' := H') (φ := φ) (u := u) (w := w))
    (hu : ((ProjectiveResolution.Hom.id P₁).comp u).cast
      (congrArg (fun ψ : S ⟶ S' => ψ.τ₁) (Category.id_comp φ)) = u)
    (hw : ((ProjectiveResolution.Hom.id P₃).comp w).cast
      (congrArg (fun ψ : S ⟶ S' => ψ.τ₃) (Category.id_comp φ)) = w) :
    ((Hom.id H).comp F).cast (Category.id_comp φ) hu hw = F :=
  HorseshoeData.Hom.ext (h := Category.id_comp F.hom)

/-- In an abelian category `C`, take short exact sequences `S,S′`,
projective endpoint resolutions `P₁,P₃` and `P₁′,P₃′`, and
horseshoe resolutions `H,H′`. Composing a comparison
`F` with the target identity comparison gives `F` after the
canonical identifications of the resolved sequence and endpoint maps. -/
theorem comp_id {S S' : ShortComplex C} {hS : S.ShortExact}
    {hS' : S'.ShortExact}
    {P₁ : ProjectiveResolution S.X₁} {P₃ : ProjectiveResolution S.X₃}
    {P₁' : ProjectiveResolution S'.X₁} {P₃' : ProjectiveResolution S'.X₃}
    {H : HorseshoeData hS P₁ P₃} {H' : HorseshoeData hS' P₁' P₃'}
    {φ : S ⟶ S'}
    {u : ProjectiveResolution.Hom P₁ P₁' φ.τ₁}
    {w : ProjectiveResolution.Hom P₃ P₃' φ.τ₃}
    (F : Hom (H := H) (H' := H') (φ := φ) (u := u) (w := w))
    (hu : (u.comp (ProjectiveResolution.Hom.id P₁')).cast
      (congrArg (fun ψ : S ⟶ S' => ψ.τ₁) (Category.comp_id φ)) = u)
    (hw : (w.comp (ProjectiveResolution.Hom.id P₃')).cast
      (congrArg (fun ψ : S ⟶ S' => ψ.τ₃) (Category.comp_id φ)) = w) :
    (F.comp (Hom.id H')).cast (Category.comp_id φ) hu hw = F :=
  HorseshoeData.Hom.ext (h := Category.comp_id F.hom)

/- Proof implementation note.
Associativity for horseshoe comparisons, transported along
`Category.assoc` of the underlying maps of short complexes, for every
choice of the endpoint transport equalities.
-/

/-- In an abelian category `C`, composition of three strict horseshoe
comparisons is associative after the canonical identification of
the sequence-map composites and supplied endpoint-resolution composites. -/
theorem assoc {S S' S'' S''' : ShortComplex C} {hS : S.ShortExact}
    {hS' : S'.ShortExact} {hS'' : S''.ShortExact}
    {hS''' : S'''.ShortExact}
    {P₁ : ProjectiveResolution S.X₁} {P₃ : ProjectiveResolution S.X₃}
    {P₁' : ProjectiveResolution S'.X₁} {P₃' : ProjectiveResolution S'.X₃}
    {P₁'' : ProjectiveResolution S''.X₁}
    {P₃'' : ProjectiveResolution S''.X₃}
    {P₁''' : ProjectiveResolution S'''.X₁}
    {P₃''' : ProjectiveResolution S'''.X₃}
    {H : HorseshoeData hS P₁ P₃} {H' : HorseshoeData hS' P₁' P₃'}
    {H'' : HorseshoeData hS'' P₁'' P₃''}
    {H''' : HorseshoeData hS''' P₁''' P₃'''}
    {φ : S ⟶ S'} {φ' : S' ⟶ S''} {φ'' : S'' ⟶ S'''}
    {u : ProjectiveResolution.Hom P₁ P₁' φ.τ₁}
    {u' : ProjectiveResolution.Hom P₁' P₁'' φ'.τ₁}
    {u'' : ProjectiveResolution.Hom P₁'' P₁''' φ''.τ₁}
    {w : ProjectiveResolution.Hom P₃ P₃' φ.τ₃}
    {w' : ProjectiveResolution.Hom P₃' P₃'' φ'.τ₃}
    {w'' : ProjectiveResolution.Hom P₃'' P₃''' φ''.τ₃}
    (F : Hom (H := H) (H' := H') (φ := φ) (u := u) (w := w))
    (G : Hom (H := H') (H' := H'') (φ := φ') (u := u') (w := w'))
    (K : Hom (H := H'') (H' := H''') (φ := φ'') (u := u'') (w := w''))
    (hu : ((u.comp u').comp u'').cast
      (congrArg (fun ψ : S ⟶ S''' => ψ.τ₁) (Category.assoc φ φ' φ'')) =
        u.comp (u'.comp u''))
    (hw : ((w.comp w').comp w'').cast
      (congrArg (fun ψ : S ⟶ S''' => ψ.τ₃) (Category.assoc φ φ' φ'')) =
        w.comp (w'.comp w'')) :
    ((F.comp G).comp K).cast (Category.assoc φ φ' φ'') hu hw =
      F.comp (G.comp K) :=
  HorseshoeData.Hom.ext (h := Category.assoc F.hom G.hom K.hom)

/- Proof implementation note.
Coordinate specification for a horseshoe comparison, lower triangular
in Mathlib's `Biprod.ofComponents` convention: the `P₁`-to-`P₃'` component
vanishes and the `P₃`-to-`P₁'` cross component is free.
-/

/-- In an abelian category `C`, take short exact sequences `S,S′`,
projective endpoint resolutions `P₁,P₃` and `P₁′,P₃′`, and
horseshoe resolutions `H,H′`. For chosen degreewise
biproduct specifications `sH,sH′`, a comparison coordinate
specification has diagonal entries `u_n,w_n`, zero corner
`P₁^n → P₃′^n`, and free corner `P₃^n → P₁′^n`. -/
structure Spec (F : HorseshoeData.Hom
    (H := H) (H' := H') (φ := φ) (u := u) (w := w)) where
  /-- In an abelian category `C`, take short exact sequences `S,S′`,
projective endpoint resolutions `P₁,P₃` and `P₁′,P₃′`, and
horseshoe resolutions `H,H′`. In the specified
biproduct coordinates, the degree-`n` middle comparison has
diagonal maps `u_n,w_n`, vanishing `P₁^n → P₃′^n` component,
and the remaining `P₃^n → P₁′^n` component. -/
  middle_f (n : ℕ) :
    (sH.middleXIso n).inv ≫ F.hom.f n ≫ (sH'.middleXIso n).hom =
      Biprod.ofComponents (u.hom.f n) 0
        (biprod.inr ≫
          ((sH.middleXIso n).inv ≫ F.hom.f n ≫
            (sH'.middleXIso n).hom) ≫ biprod.fst)
        (w.hom.f n)

/-- In an abelian category `C`, take short exact sequences `S,S′`,
projective endpoint resolutions `P₁,P₃` and `P₁′,P₃′`, and
horseshoe resolutions `H,H′`. For fixed middle
comparison `F` and fixed endpoint coordinates, any two coordinate
specifications of `F` are equal. -/
@[ext]
theorem Spec.ext {F : HorseshoeData.Hom
    (H := H) (H' := H') (φ := φ) (u := u) (w := w)}
    {s t : F.Spec (sH := sH) (sH' := sH')} : s = t := by
  cases s
  cases t
  rfl

private theorem coordinate_row
    (F : HorseshoeData.Hom
      (H := H) (H' := H') (φ := φ) (u := u) (w := w)) (n : ℕ) :
    biprod.inl ≫
        ((sH.middleXIso n).inv ≫ F.hom.f n ≫
          (sH'.middleXIso n).hom) =
      u.hom.f n ≫ biprod.inl := by
  have hi := HomologicalComplex.congr_hom F.comm_i n
  simp only [HomologicalComplex.comp_f] at hi
  calc
    _ = H.i.f n ≫ F.hom.f n ≫ (sH'.middleXIso n).hom := by
      rw [← sH.i_f]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = u.hom.f n ≫ H'.i.f n ≫ (sH'.middleXIso n).hom := by
      rw [← Category.assoc, hi, Category.assoc]
    _ = _ := by rw [sH'.i_f]

private theorem coordinate_column
    (F : HorseshoeData.Hom
      (H := H) (H' := H') (φ := φ) (u := u) (w := w)) (n : ℕ) :
    ((sH.middleXIso n).inv ≫ F.hom.f n ≫
        (sH'.middleXIso n).hom) ≫ biprod.snd =
      biprod.snd ≫ w.hom.f n := by
  have hp := HomologicalComplex.congr_hom F.comm_p n
  simp only [HomologicalComplex.comp_f] at hp
  calc
    _ = (sH.middleXIso n).inv ≫ F.hom.f n ≫ H'.p.f n := by
      rw [← sH'.p_f]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = (sH.middleXIso n).inv ≫ H.p.f n ≫ w.hom.f n := by rw [hp]
    _ = _ := by rw [← Category.assoc, sH.p_f]

/- Proof implementation note.
Every strict horseshoe comparison has the lower-triangular coordinate
formula (in Mathlib's `Biprod.ofComponents` convention: vanishing
`P₁`-to-`P₃'` component, free `P₃`-to-`P₁'` cross component) forced by its
endpoint squares.
-/

/-- In an abelian category `C`, take short exact sequences `S,S′`,
projective endpoint resolutions `P₁,P₃` and `P₁′,P₃′`, and
horseshoe resolutions `H,H′`. Every strict
comparison with supplied endpoint maps satisfies the coordinate
formula with diagonal `u_n,w_n`, zero `P₁^n → P₃′^n` corner,
and the remaining `P₃^n → P₁′^n` corner. -/
theorem spec
    (F : HorseshoeData.Hom
      (H := H) (H' := H') (φ := φ) (u := u) (w := w)) :
    F.Spec (sH := sH) (sH' := sH') := by
  refine ⟨fun n => ?_⟩
  let M := (sH.middleXIso n).inv ≫ F.hom.f n ≫
    (sH'.middleXIso n).hom
  change M = Biprod.ofComponents (u.hom.f n) 0
    (biprod.inr ≫ M ≫ biprod.fst) (w.hom.f n)
  have hrow : biprod.inl ≫ M = u.hom.f n ≫ biprod.inl :=
    coordinate_row (hS := hS) (hS' := hS')
      (P₁ := P₁) (P₃ := P₃) (P₁' := P₁') (P₃' := P₃')
      (H := H) (H' := H') (sH := sH) (sH' := sH')
      (φ := φ) (u := u) (w := w) F n
  have hcolumn : M ≫ biprod.snd = biprod.snd ≫ w.hom.f n :=
    coordinate_column (hS := hS) (hS' := hS')
      (P₁ := P₁) (P₃ := P₃) (P₁' := P₁') (P₃' := P₃')
      (H := H) (H' := H') (sH := sH) (sH' := sH')
      (φ := φ) (u := u) (w := w) F n
  have e11 : u.hom.f n = biprod.inl ≫ M ≫ biprod.fst := by
    have h := congrArg (fun k => k ≫ biprod.fst) hrow
    simpa only [Category.assoc, biprod.inl_fst, Category.comp_id]
      using h.symm
  have e12 : (0 : P₁.complex.X n ⟶ P₃'.complex.X n) =
      biprod.inl ≫ M ≫ biprod.snd := by
    have h := congrArg (fun k => k ≫ biprod.snd) hrow
    simpa only [Category.assoc, biprod.inl_snd, comp_zero]
      using h.symm
  have e22 : w.hom.f n = biprod.inr ≫ M ≫ biprod.snd := by
    have h := congrArg (fun k => biprod.inr ≫ k) hcolumn
    simpa using h.symm
  rw [e11, e12, e22]
  exact (Biprod.ofComponents_eq M).symm

end Hom
end HorseshoeData

private noncomputable def horseshoeComparisonCrossSource (n : ℕ) :
    P₃.complex.X (n + 1) ⟶ P₁.complex.X n :=
  biprod.inr ≫
    (sH.middleXIso (n + 1)).inv ≫
    H.middle.complex.d (n + 1) n ≫
    (sH.middleXIso n).hom ≫ biprod.fst

private noncomputable def horseshoeComparisonCrossTarget (n : ℕ) :
    P₃'.complex.X (n + 1) ⟶ P₁'.complex.X n :=
  biprod.inr ≫
    (sH'.middleXIso (n + 1)).inv ≫
    H'.middle.complex.d (n + 1) n ≫
    (sH'.middleXIso n).hom ≫ biprod.fst

private noncomputable def horseshoeComparisonRightAugmentationSource :
    P₃.complex.X 0 ⟶ S.X₂ :=
  biprod.inr ≫ (sH.middleXIso 0).inv ≫ H.middle.π.f 0

private noncomputable def horseshoeComparisonRightAugmentationTarget :
    P₃'.complex.X 0 ⟶ S'.X₂ :=
  biprod.inr ≫ (sH'.middleXIso 0).inv ≫ H'.middle.π.f 0

set_option backward.isDefEq.respectTransparency false in
private theorem horseshoeComparison_leftAugmentationSource :
    biprod.inl ≫ (sH.middleXIso 0).inv ≫ H.middle.π.f 0 =
      P₁.π.f 0 ≫ S.f := by
  have hi := HomologicalComplex.congr_hom H.i_augmentation 0
  simp only [HomologicalComplex.comp_f, ChainComplex.single₀_map_f_zero] at hi
  calc
    biprod.inl ≫ (sH.middleXIso 0).inv ≫ H.middle.π.f 0 =
        (H.i.f 0 ≫ (sH.middleXIso 0).hom) ≫
          (sH.middleXIso 0).inv ≫ H.middle.π.f 0 := by rw [← sH.i_f]
    _ = H.i.f 0 ≫ H.middle.π.f 0 := by simp [Category.assoc]
    _ = P₁.π.f 0 ≫ S.f := hi

set_option backward.isDefEq.respectTransparency false in
private theorem horseshoeComparison_leftAugmentationTarget :
    biprod.inl ≫ (sH'.middleXIso 0).inv ≫ H'.middle.π.f 0 =
      P₁'.π.f 0 ≫ S'.f := by
  have hi := HomologicalComplex.congr_hom H'.i_augmentation 0
  simp only [HomologicalComplex.comp_f, ChainComplex.single₀_map_f_zero] at hi
  calc
    biprod.inl ≫ (sH'.middleXIso 0).inv ≫ H'.middle.π.f 0 =
        (H'.i.f 0 ≫ (sH'.middleXIso 0).hom) ≫
          (sH'.middleXIso 0).inv ≫ H'.middle.π.f 0 := by rw [← sH'.i_f]
    _ = H'.i.f 0 ≫ H'.middle.π.f 0 := by simp [Category.assoc]
    _ = P₁'.π.f 0 ≫ S'.f := hi

set_option backward.isDefEq.respectTransparency false in
private theorem horseshoeComparison_rightAugmentationSource_comp :
    horseshoeComparisonRightAugmentationSource (H := H) (sH := sH) ≫ S.g =
      (P₃.π.f 0 : P₃.complex.X 0 ⟶ S.X₃) := by
  have hp := HomologicalComplex.congr_hom H.p_augmentation 0
  simp only [HomologicalComplex.comp_f, ChainComplex.single₀_map_f_zero] at hp
  change H.p.f 0 ≫ (P₃.π.f 0 : P₃.complex.X 0 ⟶ S.X₃) =
    H.middle.π.f 0 ≫ S.g at hp
  unfold horseshoeComparisonRightAugmentationSource
  calc
    (biprod.inr ≫ (sH.middleXIso 0).inv ≫ H.middle.π.f 0) ≫ S.g =
        biprod.inr ≫ (sH.middleXIso 0).inv ≫
          (H.middle.π.f 0 ≫ S.g) := by simp only [Category.assoc]
    _ = biprod.inr ≫ (sH.middleXIso 0).inv ≫
          (H.p.f 0 ≫ P₃.π.f 0) := by rw [← hp]
    _ = biprod.inr ≫ ((sH.middleXIso 0).inv ≫ H.p.f 0) ≫
          P₃.π.f 0 := by simp only [Category.assoc]
    _ = biprod.inr ≫ biprod.snd ≫ P₃.π.f 0 := by rw [sH.p_f]
    _ = P₃.π.f 0 := by simp

set_option backward.isDefEq.respectTransparency false in
private theorem horseshoeComparison_rightAugmentationTarget_comp :
    horseshoeComparisonRightAugmentationTarget (H' := H') (sH' := sH') ≫ S'.g =
      (P₃'.π.f 0 : P₃'.complex.X 0 ⟶ S'.X₃) := by
  have hp := HomologicalComplex.congr_hom H'.p_augmentation 0
  simp only [HomologicalComplex.comp_f, ChainComplex.single₀_map_f_zero] at hp
  change H'.p.f 0 ≫ (P₃'.π.f 0 : P₃'.complex.X 0 ⟶ S'.X₃) =
    H'.middle.π.f 0 ≫ S'.g at hp
  unfold horseshoeComparisonRightAugmentationTarget
  calc
    (biprod.inr ≫ (sH'.middleXIso 0).inv ≫ H'.middle.π.f 0) ≫ S'.g =
        biprod.inr ≫ (sH'.middleXIso 0).inv ≫
          (H'.middle.π.f 0 ≫ S'.g) := by simp only [Category.assoc]
    _ = biprod.inr ≫ (sH'.middleXIso 0).inv ≫
          (H'.p.f 0 ≫ P₃'.π.f 0) := by rw [← hp]
    _ = biprod.inr ≫ ((sH'.middleXIso 0).inv ≫ H'.p.f 0) ≫
          P₃'.π.f 0 := by simp only [Category.assoc]
    _ = biprod.inr ≫ biprod.snd ≫ P₃'.π.f 0 := by rw [sH'.p_f]
    _ = P₃'.π.f 0 := by simp

private noncomputable def horseshoeComparisonAugmentationDefectExplicit
    {S S' : ShortComplex C} (hS : S.ShortExact) (hS' : S'.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃)
    (P₁' : ProjectiveResolution S'.X₁) (P₃' : ProjectiveResolution S'.X₃)
    (H : HorseshoeData hS P₁ P₃) (H' : HorseshoeData hS' P₁' P₃')
    (sH : H.Spec) (sH' : H'.Spec) (φ : S ⟶ S')
    (w : ProjectiveResolution.Hom P₃ P₃' φ.τ₃) :
    P₃.complex.X 0 ⟶ S'.X₂ :=
  horseshoeComparisonRightAugmentationSource (H := H) (sH := sH) ≫ φ.τ₂ -
    w.hom.f 0 ≫
      horseshoeComparisonRightAugmentationTarget (H' := H') (sH' := sH')

set_option backward.isDefEq.respectTransparency false in
private theorem horseshoeComparisonAugmentationDefectExplicit_comp
    {S S' : ShortComplex C} (hS : S.ShortExact) (hS' : S'.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃)
    (P₁' : ProjectiveResolution S'.X₁) (P₃' : ProjectiveResolution S'.X₃)
    (H : HorseshoeData hS P₁ P₃) (H' : HorseshoeData hS' P₁' P₃')
    (sH : H.Spec) (sH' : H'.Spec) (φ : S ⟶ S')
    (w : ProjectiveResolution.Hom P₃ P₃' φ.τ₃) :
    horseshoeComparisonAugmentationDefectExplicit
      hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w ≫ S'.g = 0 := by
  unfold horseshoeComparisonAugmentationDefectExplicit
  rw [Preadditive.sub_comp, Category.assoc, φ.comm₂₃,
    ← Category.assoc,
    horseshoeComparison_rightAugmentationSource_comp,
    Category.assoc,
    horseshoeComparison_rightAugmentationTarget_comp]
  have hw : w.hom.f 0 ≫ (P₃'.π.f 0 : P₃'.complex.X 0 ⟶ S'.X₃) =
      (P₃.π.f 0 : P₃.complex.X 0 ⟶ S.X₃) ≫ φ.τ₃ := by
    simpa only [ChainComplex.single₀_map_f_zero] using
      w.hom_f_zero_comp_π_f_zero
  exact sub_eq_zero.mpr hw.symm

private noncomputable def horseshoeComparisonAugmentationLiftExplicit
    {S S' : ShortComplex C} (hS : S.ShortExact) (hS' : S'.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃)
    (P₁' : ProjectiveResolution S'.X₁) (P₃' : ProjectiveResolution S'.X₃)
    (H : HorseshoeData hS P₁ P₃) (H' : HorseshoeData hS' P₁' P₃')
    (sH : H.Spec) (sH' : H'.Spec) (φ : S ⟶ S')
    (w : ProjectiveResolution.Hom P₃ P₃' φ.τ₃) :
    P₃.complex.X 0 ⟶ S'.X₁ :=
  hS'.exact.liftFromProjective
    (horseshoeComparisonAugmentationDefectExplicit
      hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w)
    (horseshoeComparisonAugmentationDefectExplicit_comp
      hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w)

private theorem horseshoeComparisonAugmentationLiftExplicit_comp
    {S S' : ShortComplex C} (hS : S.ShortExact) (hS' : S'.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃)
    (P₁' : ProjectiveResolution S'.X₁) (P₃' : ProjectiveResolution S'.X₃)
    (H : HorseshoeData hS P₁ P₃) (H' : HorseshoeData hS' P₁' P₃')
    (sH : H.Spec) (sH' : H'.Spec) (φ : S ⟶ S')
    (w : ProjectiveResolution.Hom P₃ P₃' φ.τ₃) :
    horseshoeComparisonAugmentationLiftExplicit
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w ≫ S'.f =
      horseshoeComparisonAugmentationDefectExplicit
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w :=
  hS'.exact.liftFromProjective_comp _ _

private noncomputable def horseshoeComparisonCrossZeroExplicit
    {S S' : ShortComplex C} (hS : S.ShortExact) (hS' : S'.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃)
    (P₁' : ProjectiveResolution S'.X₁) (P₃' : ProjectiveResolution S'.X₃)
    (H : HorseshoeData hS P₁ P₃) (H' : HorseshoeData hS' P₁' P₃')
    (sH : H.Spec) (sH' : H'.Spec) (φ : S ⟶ S')
    (w : ProjectiveResolution.Hom P₃ P₃' φ.τ₃) :
    P₃.complex.X 0 ⟶ P₁'.complex.X 0 := by
  let e : P₁'.complex.X 0 ⟶ S'.X₁ := P₁'.π.f 0
  let _ : Epi e := epi_of_isColimit_cofork P₁'.isColimitCokernelCofork
  exact Projective.factorThru
    (horseshoeComparisonAugmentationLiftExplicit
      hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w) e

private theorem horseshoeComparisonCrossZeroExplicit_comp
    {S S' : ShortComplex C} (hS : S.ShortExact) (hS' : S'.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃)
    (P₁' : ProjectiveResolution S'.X₁) (P₃' : ProjectiveResolution S'.X₃)
    (H : HorseshoeData hS P₁ P₃) (H' : HorseshoeData hS' P₁' P₃')
    (sH : H.Spec) (sH' : H'.Spec) (φ : S ⟶ S')
    (w : ProjectiveResolution.Hom P₃ P₃' φ.τ₃) :
    horseshoeComparisonCrossZeroExplicit
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w ≫
          (P₁'.π.f 0 : P₁'.complex.X 0 ⟶ S'.X₁) =
      horseshoeComparisonAugmentationLiftExplicit
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w := by
  let e : P₁'.complex.X 0 ⟶ S'.X₁ := P₁'.π.f 0
  let _ : Epi e := epi_of_isColimit_cofork P₁'.isColimitCokernelCofork
  change Projective.factorThru
      (horseshoeComparisonAugmentationLiftExplicit
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w) e ≫ e = _
  exact Projective.factorThru_comp _ _

set_option backward.isDefEq.respectTransparency false in
private theorem horseshoeComparisonCrossZeroExplicit_augmentation
    {S S' : ShortComplex C} (hS : S.ShortExact) (hS' : S'.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃)
    (P₁' : ProjectiveResolution S'.X₁) (P₃' : ProjectiveResolution S'.X₃)
    (H : HorseshoeData hS P₁ P₃) (H' : HorseshoeData hS' P₁' P₃')
    (sH : H.Spec) (sH' : H'.Spec) (φ : S ⟶ S')
    (w : ProjectiveResolution.Hom P₃ P₃' φ.τ₃) :
    (horseshoeComparisonCrossZeroExplicit
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w ≫
          (P₁'.π.f 0 : P₁'.complex.X 0 ⟶ S'.X₁)) ≫ S'.f +
        w.hom.f 0 ≫
          horseshoeComparisonRightAugmentationTarget (H' := H') (sH' := sH') =
      horseshoeComparisonRightAugmentationSource (H := H) (sH := sH) ≫ φ.τ₂ := by
  have hCross :
      horseshoeComparisonCrossZeroExplicit
          hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w ≫
          (P₁'.π.f 0 : P₁'.complex.X 0 ⟶ S'.X₁) =
        horseshoeComparisonAugmentationLiftExplicit
          hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w :=
    horseshoeComparisonCrossZeroExplicit_comp
      hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w
  have hLift :
      horseshoeComparisonAugmentationLiftExplicit
          hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w ≫ S'.f =
        horseshoeComparisonAugmentationDefectExplicit
          hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w :=
    horseshoeComparisonAugmentationLiftExplicit_comp
      hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w
  calc
    _ = horseshoeComparisonAugmentationLiftExplicit
          hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w ≫ S'.f +
        w.hom.f 0 ≫
          horseshoeComparisonRightAugmentationTarget (H' := H') (sH' := sH') := by
      rw [hCross]
    _ = horseshoeComparisonAugmentationDefectExplicit
          hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w +
        w.hom.f 0 ≫
          horseshoeComparisonRightAugmentationTarget (H' := H') (sH' := sH') := by
      rw [hLift]
    _ = _ := by
      unfold horseshoeComparisonAugmentationDefectExplicit
      abel

set_option backward.isDefEq.respectTransparency false in
private theorem horseshoeComparisonCross_comp
    {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃)
    (H : HorseshoeData hS P₁ P₃) (sH : H.Spec) (n : ℕ) :
    horseshoeComparisonCrossSource
        (hS := hS) (P₁ := P₁) (P₃ := P₃) (H := H) (sH := sH) (n + 1) ≫
          P₁.complex.d (n + 1) n +
        P₃.complex.d (n + 2) (n + 1) ≫
          horseshoeComparisonCrossSource
            (hS := hS) (P₁ := P₁) (P₃ := P₃) (H := H) (sH := sH) n = 0 := by
  let D (k : ℕ) :=
    (sH.middleXIso (k + 1)).inv ≫
      H.middle.complex.d (k + 1) k ≫ (sH.middleXIso k).hom
  have hsq : D (n + 1) ≫ D n = 0 := by
    calc
      D (n + 1) ≫ D n =
          (sH.middleXIso (n + 2)).inv ≫
            (H.middle.complex.d (n + 2) (n + 1) ≫
              H.middle.complex.d (n + 1) n) ≫
            (sH.middleXIso n).hom := by
        dsimp only [D]
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
      _ = 0 := by rw [H.middle.complex.d_comp_d]; simp
  have hcomponent := congrArg
    (fun k => biprod.inr ≫ k ≫ biprod.fst) hsq
  dsimp only [D] at hcomponent
  rw [sH.middle_d (n + 1), sH.middle_d n] at hcomponent
  rw [show n + 1 + 1 = n + 2 by omega] at hcomponent
  simpa [horseshoeComparisonCrossSource, Category.assoc,
    Preadditive.comp_add] using hcomponent

set_option backward.isDefEq.respectTransparency false in
private theorem horseshoeComparisonCross_comp_leftAugmentation
    {S : ShortComplex C} (hS : S.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃)
    (H : HorseshoeData hS P₁ P₃) (sH : H.Spec) :
    horseshoeComparisonCrossSource
        (hS := hS) (P₁ := P₁) (P₃ := P₃) (H := H) (sH := sH) 0 ≫
        P₁.π.f 0 ≫ S.f +
        P₃.complex.d 1 0 ≫
          horseshoeComparisonRightAugmentationSource (H := H) (sH := sH) = 0 := by
  have hπ := H.middle.π.comm 1 0
  have hzero : H.middle.complex.d 1 0 ≫
      (H.middle.π.f 0 : H.middle.complex.X 0 ⟶ S.X₂) = 0 := by
    simpa only [HomologicalComplex.single_obj_d, comp_zero] using hπ.symm
  let D := (sH.middleXIso 1).inv ≫ H.middle.complex.d 1 0 ≫
    (sH.middleXIso 0).hom
  have hcomponent :
      biprod.inr ≫ D ≫ (sH.middleXIso 0).inv ≫
        (H.middle.π.f 0 : H.middle.complex.X 0 ⟶ S.X₂) = 0 := by
    dsimp only [D]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, comp_zero] using
      congrArg (fun k => biprod.inr ≫ (sH.middleXIso 1).inv ≫ k) hzero
  dsimp only [D] at hcomponent
  rw [sH.middle_d 0] at hcomponent
  rw [← Category.assoc, Biprod.inr_ofComponents] at hcomponent
  simpa [horseshoeComparisonCrossSource,
    horseshoeComparisonRightAugmentationSource,
    horseshoeComparison_leftAugmentationSource,
    Category.assoc, Preadditive.add_comp] using hcomponent

private noncomputable def horseshoeComparisonCrossTargetTermExplicit
    {S S' : ShortComplex C} (hS : S.ShortExact) (hS' : S'.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃)
    (P₁' : ProjectiveResolution S'.X₁) (P₃' : ProjectiveResolution S'.X₃)
    (H : HorseshoeData hS P₁ P₃) (H' : HorseshoeData hS' P₁' P₃')
    (sH : H.Spec) (sH' : H'.Spec) (φ : S ⟶ S')
    (u : ProjectiveResolution.Hom P₁ P₁' φ.τ₁)
    (w : ProjectiveResolution.Hom P₃ P₃' φ.τ₃)
    (n : ℕ) (μ : P₃.complex.X n ⟶ P₁'.complex.X n) :
    P₃.complex.X (n + 1) ⟶ P₁'.complex.X n :=
  horseshoeComparisonCrossSource
      (hS := hS) (P₁ := P₁) (P₃ := P₃) (H := H) (sH := sH) n ≫
      u.hom.f n +
    P₃.complex.d (n + 1) n ≫ μ -
    w.hom.f (n + 1) ≫
      horseshoeComparisonCrossTarget
        (hS' := hS') (P₁' := P₁') (P₃' := P₃')
        (H' := H') (sH' := sH') n

set_option backward.isDefEq.respectTransparency false in
private theorem horseshoeComparisonCrossTargetTermZero_cycle
    {S S' : ShortComplex C} (hS : S.ShortExact) (hS' : S'.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃)
    (P₁' : ProjectiveResolution S'.X₁) (P₃' : ProjectiveResolution S'.X₃)
    (H : HorseshoeData hS P₁ P₃) (H' : HorseshoeData hS' P₁' P₃')
    (sH : H.Spec) (sH' : H'.Spec) (φ : S ⟶ S')
    (u : ProjectiveResolution.Hom P₁ P₁' φ.τ₁)
    (w : ProjectiveResolution.Hom P₃ P₃' φ.τ₃) :
    horseshoeComparisonCrossTargetTermExplicit
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w 0
        (horseshoeComparisonCrossZeroExplicit
          hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w) ≫
      (P₁'.π.f 0 : P₁'.complex.X 0 ⟶ S'.X₁) = 0 := by
  let μ₀ := horseshoeComparisonCrossZeroExplicit
    hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w
  let b := horseshoeComparisonRightAugmentationSource (H := H) (sH := sH)
  let b' := horseshoeComparisonRightAugmentationTarget (H' := H') (sH' := sH')
  have hSource := horseshoeComparisonCross_comp_leftAugmentation
    hS P₁ P₃ H sH
  have hTarget := horseshoeComparisonCross_comp_leftAugmentation
    hS' P₁' P₃' H' sH'
  have hSource' :
      horseshoeComparisonCrossSource
          (hS := hS) (P₁ := P₁) (P₃ := P₃) (H := H) (sH := sH) 0 ≫
          P₁.π.f 0 ≫ S.f = -(P₃.complex.d 1 0 ≫ b) :=
    add_eq_zero_iff_eq_neg.mp hSource
  have hTarget' :
      horseshoeComparisonCrossTarget
          (hS' := hS') (P₁' := P₁') (P₃' := P₃')
          (H' := H') (sH' := sH') 0 ≫ P₁'.π.f 0 ≫ S'.f =
        -(P₃'.complex.d 1 0 ≫ b') :=
    add_eq_zero_iff_eq_neg.mp hTarget
  have hμ := horseshoeComparisonCrossZeroExplicit_augmentation
    hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w
  have hμ' : μ₀ ≫ P₁'.π.f 0 ≫ S'.f =
      b ≫ φ.τ₂ - w.hom.f 0 ≫ b' := by
    dsimp only [μ₀, b, b']
    rw [← Category.assoc]
    rw [← hμ]
    abel
  have hu := u.hom_f_zero_comp_π_f_zero
  have hu' : u.hom.f 0 ≫ (P₁'.π.f 0 : P₁'.complex.X 0 ⟶ S'.X₁) =
      (P₁.π.f 0 : P₁.complex.X 0 ⟶ S.X₁) ≫ φ.τ₁ := by
    simpa only [ChainComplex.single₀_map_f_zero] using hu
  have hw := w.hom.comm 1 0
  let _ : Mono S'.f := hS'.mono_f
  apply (cancel_mono S'.f).1
  change
    (horseshoeComparisonCrossTargetTermExplicit
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w 0
          (horseshoeComparisonCrossZeroExplicit
            hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w) ≫
      (P₁'.π.f 0 : P₁'.complex.X 0 ⟶ S'.X₁)) ≫ S'.f = 0
        ≫ S'.f
  rw [zero_comp]
  unfold horseshoeComparisonCrossTargetTermExplicit
  have hFirst :
      ((horseshoeComparisonCrossSource
            (hS := hS) (P₁ := P₁) (P₃ := P₃) (H := H) (sH := sH) 0 ≫
          u.hom.f 0) ≫ (P₁'.π.f 0 : P₁'.complex.X 0 ⟶ S'.X₁)) ≫ S'.f =
        ((horseshoeComparisonCrossSource
              (hS := hS) (P₁ := P₁) (P₃ := P₃) (H := H) (sH := sH) 0 ≫
            (P₁.π.f 0 : P₁.complex.X 0 ⟶ S.X₁)) ≫ S.f) ≫ φ.τ₂ := by
    calc
      _ = horseshoeComparisonCrossSource
            (hS := hS) (P₁ := P₁) (P₃ := P₃) (H := H) (sH := sH) 0 ≫
          ((u.hom.f 0 ≫ (P₁'.π.f 0 : P₁'.complex.X 0 ⟶ S'.X₁)) ≫ S'.f) := by
            simp only [Category.assoc]
      _ = horseshoeComparisonCrossSource
            (hS := hS) (P₁ := P₁) (P₃ := P₃) (H := H) (sH := sH) 0 ≫
          (((P₁.π.f 0 : P₁.complex.X 0 ⟶ S.X₁) ≫ φ.τ₁) ≫ S'.f) := by
            rw [hu']
      _ = ((horseshoeComparisonCrossSource
              (hS := hS) (P₁ := P₁) (P₃ := P₃) (H := H) (sH := sH) 0 ≫
            (P₁.π.f 0 : P₁.complex.X 0 ⟶ S.X₁)) ≫ S.f) ≫ φ.τ₂ := by
            simp only [Category.assoc, φ.comm₁₂]
  have hSourceFull :
      (horseshoeComparisonCrossSource
          (hS := hS) (P₁ := P₁) (P₃ := P₃) (H := H) (sH := sH) 0 ≫
        (P₁.π.f 0 : P₁.complex.X 0 ⟶ S.X₁)) ≫ S.f =
        -(P₃.complex.d 1 0 ≫ b) := by
    calc
      _ = horseshoeComparisonCrossSource
            (hS := hS) (P₁ := P₁) (P₃ := P₃) (H := H) (sH := sH) 0 ≫
          (P₁.π.f 0 : P₁.complex.X 0 ⟶ S.X₁) ≫ S.f :=
        Category.assoc _ _ _
      _ = _ := hSource'
  rw [Preadditive.sub_comp, Preadditive.add_comp,
    Preadditive.sub_comp, Preadditive.add_comp]
  rw [hFirst, hSourceFull]
  simp only [Category.assoc]
  rw [hμ', hTarget']
  have hSourceNeg : (-(P₃.complex.d 1 0 ≫ b)) ≫ φ.τ₂ =
      -(P₃.complex.d 1 0 ≫ (b ≫ φ.τ₂)) := by
    rw [Preadditive.neg_comp, Category.assoc]
  have hMiddleSub :
      P₃.complex.d 1 0 ≫ (b ≫ φ.τ₂ - w.hom.f 0 ≫ b') =
        P₃.complex.d 1 0 ≫ (b ≫ φ.τ₂) -
          P₃.complex.d 1 0 ≫ (w.hom.f 0 ≫ b') := by
    rw [Preadditive.comp_sub]
  have hTargetComp :
      w.hom.f 1 ≫ (P₃'.complex.d 1 0 ≫ b') =
        P₃.complex.d 1 0 ≫ (w.hom.f 0 ≫ b') := by
    calc
      _ = (w.hom.f 1 ≫ P₃'.complex.d 1 0) ≫ b' :=
        (Category.assoc _ _ _).symm
      _ = (P₃.complex.d 1 0 ≫ w.hom.f 0) ≫ b' := by rw [hw]
      _ = _ := Category.assoc _ _ _
  have hTargetNeg : w.hom.f 1 ≫ (-(P₃'.complex.d 1 0 ≫ b')) =
      -(P₃.complex.d 1 0 ≫ (w.hom.f 0 ≫ b')) := by
    rw [Preadditive.comp_neg, hTargetComp]
  rw [hSourceNeg, hMiddleSub, hTargetNeg]
  abel

private noncomputable def horseshoeComparisonCrossOneExplicit
    {S S' : ShortComplex C} (hS : S.ShortExact) (hS' : S'.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃)
    (P₁' : ProjectiveResolution S'.X₁) (P₃' : ProjectiveResolution S'.X₃)
    (H : HorseshoeData hS P₁ P₃) (H' : HorseshoeData hS' P₁' P₃')
    (sH : H.Spec) (sH' : H'.Spec) (φ : S ⟶ S')
    (u : ProjectiveResolution.Hom P₁ P₁' φ.τ₁)
    (w : ProjectiveResolution.Hom P₃ P₃' φ.τ₃) :
    P₃.complex.X 1 ⟶ P₁'.complex.X 1 :=
  P₁'.exact₀.liftFromProjective
    (horseshoeComparisonCrossTargetTermExplicit
      hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w 0
      (horseshoeComparisonCrossZeroExplicit
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w))
    (horseshoeComparisonCrossTargetTermZero_cycle
      hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w)

private theorem horseshoeComparisonCrossOneExplicit_comp
    {S S' : ShortComplex C} (hS : S.ShortExact) (hS' : S'.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃)
    (P₁' : ProjectiveResolution S'.X₁) (P₃' : ProjectiveResolution S'.X₃)
    (H : HorseshoeData hS P₁ P₃) (H' : HorseshoeData hS' P₁' P₃')
    (sH : H.Spec) (sH' : H'.Spec) (φ : S ⟶ S')
    (u : ProjectiveResolution.Hom P₁ P₁' φ.τ₁)
    (w : ProjectiveResolution.Hom P₃ P₃' φ.τ₃) :
    horseshoeComparisonCrossOneExplicit
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w ≫
      P₁'.complex.d 1 0 =
    horseshoeComparisonCrossTargetTermExplicit
      hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w 0
      (horseshoeComparisonCrossZeroExplicit
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w) :=
  P₁'.exact₀.liftFromProjective_comp _ _

set_option backward.isDefEq.respectTransparency false in
private theorem horseshoeComparisonCrossTargetTermExplicit_cycle
    {S S' : ShortComplex C} (hS : S.ShortExact) (hS' : S'.ShortExact)
    (P₁ : ProjectiveResolution S.X₁) (P₃ : ProjectiveResolution S.X₃)
    (P₁' : ProjectiveResolution S'.X₁) (P₃' : ProjectiveResolution S'.X₃)
    (H : HorseshoeData hS P₁ P₃) (H' : HorseshoeData hS' P₁' P₃')
    (sH : H.Spec) (sH' : H'.Spec) (phi : S ⟶ S')
    (u : ProjectiveResolution.Hom P₁ P₁' phi.τ₁)
    (w : ProjectiveResolution.Hom P₃ P₃' phi.τ₃)
    (n : ℕ) (mu : P₃.complex.X n ⟶ P₁'.complex.X n)
    (mu' : P₃.complex.X (n + 1) ⟶ P₁'.complex.X (n + 1))
    (hmu : mu' ≫ P₁'.complex.d (n + 1) n =
      horseshoeComparisonCrossTargetTermExplicit
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' phi u w n mu) :
    horseshoeComparisonCrossTargetTermExplicit
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' phi u w (n + 1) mu' ≫
      P₁'.complex.d (n + 1) n = 0 := by
  have hSource := add_eq_zero_iff_eq_neg.mp
    (horseshoeComparisonCross_comp hS P₁ P₃ H sH n)
  have hTarget := add_eq_zero_iff_eq_neg.mp
    (horseshoeComparisonCross_comp hS' P₁' P₃' H' sH' n)
  have hSourcePost :
      horseshoeComparisonCrossSource
          (hS := hS) (P₁ := P₁) (P₃ := P₃) (H := H) (sH := sH) (n + 1) ≫
          (P₁.complex.d (n + 1) n ≫ u.hom.f n) =
        -(P₃.complex.d (n + 2) (n + 1) ≫
          (horseshoeComparisonCrossSource
            (hS := hS) (P₁ := P₁) (P₃ := P₃) (H := H) (sH := sH) n ≫
              u.hom.f n)) := by
    calc
      _ = (horseshoeComparisonCrossSource
              (hS := hS) (P₁ := P₁) (P₃ := P₃) (H := H) (sH := sH)
              (n + 1) ≫ P₁.complex.d (n + 1) n) ≫ u.hom.f n :=
        (Category.assoc _ _ _).symm
      _ = (-(P₃.complex.d (n + 2) (n + 1) ≫
          horseshoeComparisonCrossSource
            (hS := hS) (P₁ := P₁) (P₃ := P₃) (H := H) (sH := sH) n)) ≫
            u.hom.f n := by rw [hSource]
      _ = _ := by rw [Preadditive.neg_comp, Category.assoc]
  have hTargetPre :
      w.hom.f (n + 2) ≫
          (horseshoeComparisonCrossTarget
              (hS' := hS') (P₁' := P₁') (P₃' := P₃')
              (H' := H') (sH' := sH') (n + 1) ≫
            P₁'.complex.d (n + 1) n) =
        -(P₃.complex.d (n + 2) (n + 1) ≫
          (w.hom.f (n + 1) ≫
            horseshoeComparisonCrossTarget
              (hS' := hS') (P₁' := P₁') (P₃' := P₃')
              (H' := H') (sH' := sH') n)) := by
    have hTargetInner :
        horseshoeComparisonCrossTarget
              (hS' := hS') (P₁' := P₁') (P₃' := P₃')
              (H' := H') (sH' := sH') (n + 1) ≫
            P₁'.complex.d (n + 1) n =
          -(P₃'.complex.d (n + 2) (n + 1) ≫
            horseshoeComparisonCrossTarget
              (hS' := hS') (P₁' := P₁') (P₃' := P₃')
              (H' := H') (sH' := sH') n) := hTarget
    calc
      _ = (w.hom.f (n + 2) ≫
          horseshoeComparisonCrossTarget
              (hS' := hS') (P₁' := P₁') (P₃' := P₃')
              (H' := H') (sH' := sH') (n + 1)) ≫
            P₁'.complex.d (n + 1) n := (Category.assoc _ _ _).symm
      _ = w.hom.f (n + 2) ≫
          (horseshoeComparisonCrossTarget
                (hS' := hS') (P₁' := P₁') (P₃' := P₃')
                (H' := H') (sH' := sH') (n + 1) ≫
            P₁'.complex.d (n + 1) n) := Category.assoc _ _ _
      _ = w.hom.f (n + 2) ≫
          (-(P₃'.complex.d (n + 2) (n + 1) ≫
            horseshoeComparisonCrossTarget
              (hS' := hS') (P₁' := P₁') (P₃' := P₃')
              (H' := H') (sH' := sH') n)) := by
            exact congrArg
              (fun k : P₃'.complex.X (n + 2) ⟶ P₁'.complex.X n =>
                w.hom.f (n + 2) ≫ k) hTargetInner
      _ = -(w.hom.f (n + 2) ≫
          (P₃'.complex.d (n + 2) (n + 1) ≫
            horseshoeComparisonCrossTarget
              (hS' := hS') (P₁' := P₁') (P₃' := P₃')
              (H' := H') (sH' := sH') n)) := by rw [Preadditive.comp_neg]
      _ = -((w.hom.f (n + 2) ≫ P₃'.complex.d (n + 2) (n + 1)) ≫
          horseshoeComparisonCrossTarget
            (hS' := hS') (P₁' := P₁') (P₃' := P₃')
            (H' := H') (sH' := sH') n) := by rw [Category.assoc]
      _ = -((P₃.complex.d (n + 2) (n + 1) ≫ w.hom.f (n + 1)) ≫
          horseshoeComparisonCrossTarget
            (hS' := hS') (P₁' := P₁') (P₃' := P₃')
            (H' := H') (sH' := sH') n) := by rw [w.hom.comm]
      _ = _ := by rw [Category.assoc]
  have hDD : P₃.complex.d (n + 2) (n + 1) ≫
      (P₃.complex.d (n + 1) n ≫ mu) = 0 := by
    rw [← Category.assoc, P₃.complex.d_comp_d, zero_comp]
  unfold horseshoeComparisonCrossTargetTermExplicit
  rw [Preadditive.sub_comp, Preadditive.add_comp]
  simp only [Category.assoc]
  rw [u.hom.comm (n + 1) n, hmu, hSourcePost, hTargetPre]
  unfold horseshoeComparisonCrossTargetTermExplicit
  rw [Preadditive.comp_sub, Preadditive.comp_add, hDD]
  abel

private noncomputable def horseshoeComparisonCrossAuxExplicit : ∀ n : ℕ,
    Σ' (mu : P₃.complex.X n ⟶ P₁'.complex.X n)
      (mu' : P₃.complex.X (n + 1) ⟶ P₁'.complex.X (n + 1)),
      mu' ≫ P₁'.complex.d (n + 1) n =
        horseshoeComparisonCrossTargetTermExplicit
          hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n mu
  | 0 =>
      ⟨horseshoeComparisonCrossZeroExplicit
          hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w,
        horseshoeComparisonCrossOneExplicit
          hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w,
        horseshoeComparisonCrossOneExplicit_comp
          hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w⟩
  | n + 1 =>
      let I := horseshoeComparisonCrossAuxExplicit n
      let g := horseshoeComparisonCrossTargetTermExplicit
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w (n + 1) I.2.1
      have hg : g ≫ P₁'.complex.d (n + 1) n = 0 :=
        horseshoeComparisonCrossTargetTermExplicit_cycle
          hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n I.1 I.2.1 I.2.2
      let mu'' := (P₁'.exact_succ n).liftFromProjective g hg
      ⟨I.2.1, mu'', by
        dsimp only [mu'', g]
        rw [(P₁'.exact_succ n).liftFromProjective_comp]⟩

private noncomputable def horseshoeComparisonCrossExplicit (n : ℕ) :
    P₃.complex.X n ⟶ P₁'.complex.X n :=
  (horseshoeComparisonCrossAuxExplicit
    hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n).1

private theorem horseshoeComparisonCrossExplicit_zero :
    horseshoeComparisonCrossExplicit
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w 0 =
      horseshoeComparisonCrossZeroExplicit
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w := by
  rfl

private theorem horseshoeComparisonCrossExplicit_succ (n : ℕ) :
    horseshoeComparisonCrossExplicit
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w (n + 1) =
      (horseshoeComparisonCrossAuxExplicit
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n).2.1 := by
  rfl

private theorem horseshoeComparisonCrossExplicit_comp (n : ℕ) :
    horseshoeComparisonCrossExplicit
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w (n + 1) ≫
        P₁'.complex.d (n + 1) n =
      horseshoeComparisonCrossTargetTermExplicit
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n
          (horseshoeComparisonCrossExplicit
            hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n) := by
  rw [horseshoeComparisonCrossExplicit_succ]
  exact (horseshoeComparisonCrossAuxExplicit
    hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n).2.2

private noncomputable def horseshoeComparisonMiddleMatrix (n : ℕ) :
    (P₁.complex.X n ⊞ P₃.complex.X n) ⟶
      (P₁'.complex.X n ⊞ P₃'.complex.X n) :=
  Biprod.ofComponents (u.hom.f n) 0
    (horseshoeComparisonCrossExplicit
      hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n)
    (w.hom.f n)

set_option backward.isDefEq.respectTransparency false in
private theorem horseshoeComparisonMiddleMatrix_comm (n : ℕ) :
    horseshoeComparisonMiddleMatrix
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w (n + 1) ≫
      Biprod.ofComponents (P₁'.complex.d (n + 1) n) 0
        (horseshoeComparisonCrossTarget
          (hS' := hS') (P₁' := P₁') (P₃' := P₃')
          (H' := H') (sH' := sH') n)
        (P₃'.complex.d (n + 1) n) =
    Biprod.ofComponents (P₁.complex.d (n + 1) n) 0
        (horseshoeComparisonCrossSource
          (hS := hS) (P₁ := P₁) (P₃ := P₃)
          (H := H) (sH := sH) n)
        (P₃.complex.d (n + 1) n) ≫
      horseshoeComparisonMiddleMatrix
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n := by
  apply biprod.hom_ext
  · apply biprod.hom_ext'
    · simp [horseshoeComparisonMiddleMatrix]
    · simp [horseshoeComparisonMiddleMatrix,
        horseshoeComparisonCrossTargetTermExplicit,
        horseshoeComparisonCrossExplicit_comp]
  · apply biprod.hom_ext'
    · simp [horseshoeComparisonMiddleMatrix]
    · simp [horseshoeComparisonMiddleMatrix]

private noncomputable def horseshoeComparisonMiddleComponent (n : ℕ) :
    H.middle.complex.X n ⟶ H'.middle.complex.X n :=
  (sH.middleXIso n).hom ≫
    horseshoeComparisonMiddleMatrix
      hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n ≫
    (sH'.middleXIso n).inv

private theorem horseshoeComparisonMiddleComponent_coordinate (n : ℕ) :
    (sH.middleXIso n).inv ≫
        horseshoeComparisonMiddleComponent
          hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n ≫
        (sH'.middleXIso n).hom =
      horseshoeComparisonMiddleMatrix
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n := by
  unfold horseshoeComparisonMiddleComponent
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
private theorem horseshoeComparisonMiddleComponent_comm (n : ℕ) :
    horseshoeComparisonMiddleComponent
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w (n + 1) ≫
        H'.middle.complex.d (n + 1) n =
      H.middle.complex.d (n + 1) n ≫
        horseshoeComparisonMiddleComponent
          hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n := by
  apply (cancel_epi (sH.middleXIso (n + 1)).inv).1
  apply (cancel_mono (sH'.middleXIso n).hom).1
  unfold horseshoeComparisonMiddleComponent
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id]
  have hSourceCross :
      biprod.inr ≫
          (((sH.middleXIso (n + 1)).inv ≫
              H.middle.complex.d (n + 1) n ≫ (sH.middleXIso n).hom) ≫
            biprod.fst) =
        horseshoeComparisonCrossSource
          (hS := hS) (P₁ := P₁) (P₃ := P₃) (H := H) (sH := sH) n := by
    simp only [horseshoeComparisonCrossSource, Category.assoc]
  have hTargetCross :
      biprod.inr ≫
          (((sH'.middleXIso (n + 1)).inv ≫
              H'.middle.complex.d (n + 1) n ≫ (sH'.middleXIso n).hom) ≫
            biprod.fst) =
        horseshoeComparisonCrossTarget
          (hS' := hS') (P₁' := P₁') (P₃' := P₃')
          (H' := H') (sH' := sH') n := by
    simp only [horseshoeComparisonCrossTarget, Category.assoc]
  calc
    horseshoeComparisonMiddleMatrix
          hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w (n + 1) ≫
        ((sH'.middleXIso (n + 1)).inv ≫
          H'.middle.complex.d (n + 1) n ≫ (sH'.middleXIso n).hom) =
      ((sH.middleXIso (n + 1)).inv ≫
          H.middle.complex.d (n + 1) n ≫ (sH.middleXIso n).hom) ≫
        horseshoeComparisonMiddleMatrix
          hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n := by
      rw [sH'.middle_d n, sH.middle_d n]
      rw [hTargetCross, hSourceCross]
      exact horseshoeComparisonMiddleMatrix_comm
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n
    _ = (sH.middleXIso (n + 1)).inv ≫
        H.middle.complex.d (n + 1) n ≫ (sH.middleXIso n).hom ≫
          horseshoeComparisonMiddleMatrix
            hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n := by
      simp only [Category.assoc]

private noncomputable def horseshoeComparisonMiddleHom :
    H.middle.complex ⟶ H'.middle.complex :=
  ChainComplex.ofHom
    (fun n => horseshoeComparisonMiddleComponent
      hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n)
    (fun n => horseshoeComparisonMiddleComponent_comm
      hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n)

private theorem horseshoeComparisonMiddleComponent_comm_i (n : ℕ) :
    H.i.f n ≫
        horseshoeComparisonMiddleComponent
          hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n =
      u.hom.f n ≫ H'.i.f n := by
  unfold horseshoeComparisonMiddleComponent horseshoeComparisonMiddleMatrix
  calc
    _ = ((H.i.f n ≫ (sH.middleXIso n).hom) ≫
          Biprod.ofComponents (u.hom.f n) 0
            (horseshoeComparisonCrossExplicit
              hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n)
            (w.hom.f n)) ≫ (sH'.middleXIso n).inv := by
      simp only [Category.assoc]
    _ = (biprod.inl ≫
          Biprod.ofComponents (u.hom.f n) 0
            (horseshoeComparisonCrossExplicit
              hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n)
            (w.hom.f n)) ≫ (sH'.middleXIso n).inv := by rw [sH.i_f]
    _ = (u.hom.f n ≫ biprod.inl) ≫ (sH'.middleXIso n).inv := by simp
    _ = (u.hom.f n ≫ (H'.i.f n ≫ (sH'.middleXIso n).hom)) ≫
        (sH'.middleXIso n).inv := by rw [sH'.i_f]
    _ = u.hom.f n ≫ H'.i.f n := by simp [Category.assoc]

private theorem horseshoeComparisonMiddleComponent_comm_p (n : ℕ) :
    horseshoeComparisonMiddleComponent
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n ≫
        H'.p.f n =
      H.p.f n ≫ w.hom.f n := by
  unfold horseshoeComparisonMiddleComponent horseshoeComparisonMiddleMatrix
  calc
    _ = (sH.middleXIso n).hom ≫
        (Biprod.ofComponents (u.hom.f n) 0
            (horseshoeComparisonCrossExplicit
              hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n)
            (w.hom.f n) ≫
          ((sH'.middleXIso n).inv ≫ H'.p.f n)) := by
      simp only [Category.assoc]
    _ = (sH.middleXIso n).hom ≫
        (Biprod.ofComponents (u.hom.f n) 0
            (horseshoeComparisonCrossExplicit
              hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n)
            (w.hom.f n) ≫ biprod.snd) := by rw [sH'.p_f]
    _ = (sH.middleXIso n).hom ≫ (biprod.snd ≫ w.hom.f n) := by simp
    _ = (sH.middleXIso n).hom ≫
        (((sH.middleXIso n).inv ≫ H.p.f n) ≫ w.hom.f n) := by rw [sH.p_f]
    _ = H.p.f n ≫ w.hom.f n := by simp [Category.assoc]

private theorem horseshoeComparisonMiddleHom_comm_i :
    H.i ≫ horseshoeComparisonMiddleHom
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w =
      u.hom ≫ H'.i := by
  ext n
  exact horseshoeComparisonMiddleComponent_comm_i
    hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n

private theorem horseshoeComparisonMiddleHom_comm_p :
    horseshoeComparisonMiddleHom
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w ≫ H'.p =
      H.p ≫ w.hom := by
  ext n
  exact horseshoeComparisonMiddleComponent_comm_p
    hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n

set_option backward.isDefEq.respectTransparency false in
private theorem horseshoeComparisonMiddleComponent_zero_augmentation :
    horseshoeComparisonMiddleComponent
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w 0 ≫
        H'.middle.π.f 0 =
      H.middle.π.f 0 ≫ φ.τ₂ := by
  have hu : u.hom.f 0 ≫ (P₁'.π.f 0 : P₁'.complex.X 0 ⟶ S'.X₁) =
      (P₁.π.f 0 : P₁.complex.X 0 ⟶ S.X₁) ≫ φ.τ₁ := by
    simpa only [ChainComplex.single₀_map_f_zero] using
      u.hom_f_zero_comp_π_f_zero
  have hLeft :
      u.hom.f 0 ≫ ((P₁'.π.f 0 : P₁'.complex.X 0 ⟶ S'.X₁) ≫ S'.f) =
        ((P₁.π.f 0 : P₁.complex.X 0 ⟶ S.X₁) ≫ S.f) ≫ φ.τ₂ := by
    calc
      _ = (u.hom.f 0 ≫ (P₁'.π.f 0 : P₁'.complex.X 0 ⟶ S'.X₁)) ≫
          S'.f := (Category.assoc _ _ _).symm
      _ = ((P₁.π.f 0 : P₁.complex.X 0 ⟶ S.X₁) ≫ φ.τ₁) ≫ S'.f := by
        rw [hu]
      _ = (P₁.π.f 0 : P₁.complex.X 0 ⟶ S.X₁) ≫
          (φ.τ₁ ≫ S'.f) := Category.assoc _ _ _
      _ = (P₁.π.f 0 : P₁.complex.X 0 ⟶ S.X₁) ≫
          (S.f ≫ φ.τ₂) := by rw [φ.comm₁₂]
      _ = _ := (Category.assoc _ _ _).symm
  have hLower :
      (horseshoeComparisonCrossExplicit
          hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w 0 ≫
          (P₁'.π.f 0 : P₁'.complex.X 0 ⟶ S'.X₁)) ≫ S'.f +
        w.hom.f 0 ≫
          horseshoeComparisonRightAugmentationTarget (H' := H') (sH' := sH') =
      horseshoeComparisonRightAugmentationSource (H := H) (sH := sH) ≫ φ.τ₂ := by
    rw [horseshoeComparisonCrossExplicit_zero]
    exact horseshoeComparisonCrossZeroExplicit_augmentation
      hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ w
  have hTargetLeft :
      u.hom.f 0 ≫
          (biprod.inl ≫
            ((sH'.middleXIso 0).inv ≫ H'.middle.π.f 0)) =
        u.hom.f 0 ≫
          ((P₁'.π.f 0 : P₁'.complex.X 0 ⟶ S'.X₁) ≫ S'.f) :=
    congrArg
      (fun k : P₁'.complex.X 0 ⟶ S'.X₂ => u.hom.f 0 ≫ k)
      (horseshoeComparison_leftAugmentationTarget hS' P₁' P₃' H' sH')
  have hSourceLeft :
      biprod.inl ≫
          ((sH.middleXIso 0).inv ≫ (H.middle.π.f 0 ≫ φ.τ₂)) =
        ((P₁.π.f 0 : P₁.complex.X 0 ⟶ S.X₁) ≫ S.f) ≫ φ.τ₂ := by
    calc
      _ = (biprod.inl ≫ (sH.middleXIso 0).inv ≫ H.middle.π.f 0) ≫
          φ.τ₂ := by simp only [Category.assoc]
      _ = _ := congrArg
        (fun k : P₁.complex.X 0 ⟶ S.X₂ => k ≫ φ.τ₂)
        (horseshoeComparison_leftAugmentationSource hS P₁ P₃ H sH)
  have hTargetRight :
      biprod.inr ≫ ((sH'.middleXIso 0).inv ≫ H'.middle.π.f 0) =
        horseshoeComparisonRightAugmentationTarget (H' := H') (sH' := sH') := by
    simp only [horseshoeComparisonRightAugmentationTarget]
  have hSourceRight :
      biprod.inr ≫ ((sH.middleXIso 0).inv ≫ H.middle.π.f 0) =
        horseshoeComparisonRightAugmentationSource (H := H) (sH := sH) := by
    simp only [horseshoeComparisonRightAugmentationSource]
  have hCrossTarget :
      horseshoeComparisonCrossExplicit
          hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w 0 ≫
          (biprod.inl ≫ ((sH'.middleXIso 0).inv ≫ H'.middle.π.f 0)) =
        (horseshoeComparisonCrossExplicit
            hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w 0 ≫
            (P₁'.π.f 0 : P₁'.complex.X 0 ⟶ S'.X₁)) ≫ S'.f := by
    calc
      _ = horseshoeComparisonCrossExplicit
            hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w 0 ≫
          ((P₁'.π.f 0 : P₁'.complex.X 0 ⟶ S'.X₁) ≫ S'.f) :=
        congrArg
          (fun k : P₁'.complex.X 0 ⟶ S'.X₂ =>
            horseshoeComparisonCrossExplicit
              hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w 0 ≫ k)
          (horseshoeComparison_leftAugmentationTarget hS' P₁' P₃' H' sH')
      _ = _ := (Category.assoc _ _ _).symm
  have hWTarget :
      w.hom.f 0 ≫
          (biprod.inr ≫ ((sH'.middleXIso 0).inv ≫ H'.middle.π.f 0)) =
        w.hom.f 0 ≫
          horseshoeComparisonRightAugmentationTarget (H' := H') (sH' := sH') :=
    congrArg
      (fun k : P₃'.complex.X 0 ⟶ S'.X₂ => w.hom.f 0 ≫ k)
      hTargetRight
  have hSourceRightPost :
      biprod.inr ≫
          ((sH.middleXIso 0).inv ≫ (H.middle.π.f 0 ≫ φ.τ₂)) =
        horseshoeComparisonRightAugmentationSource (H := H) (sH := sH) ≫ φ.τ₂ := by
    calc
      _ = (biprod.inr ≫ (sH.middleXIso 0).inv ≫ H.middle.π.f 0) ≫
          φ.τ₂ := by simp only [Category.assoc]
      _ = _ := congrArg
        (fun k : P₃.complex.X 0 ⟶ S.X₂ => k ≫ φ.τ₂) hSourceRight
  apply (cancel_epi (sH.middleXIso 0).inv).1
  unfold horseshoeComparisonMiddleComponent horseshoeComparisonMiddleMatrix
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  apply biprod.hom_ext'
  · rw [← Category.assoc, Biprod.inl_ofComponents]
    simp only [zero_comp, add_zero, Category.assoc]
    exact hTargetLeft.trans (hLeft.trans hSourceLeft.symm)
  · rw [← Category.assoc, Biprod.inr_ofComponents]
    simp only [Preadditive.add_comp, Category.assoc]
    exact (congrArg₂ (fun a b => a + b) hCrossTarget hWTarget).trans
      (hLower.trans hSourceRightPost.symm)

private theorem horseshoeComparisonMiddleHom_augmentation :
    horseshoeComparisonMiddleHom
        hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w ≫ H'.middle.π =
      H.middle.π ≫ (ChainComplex.single₀ C).map φ.τ₂ := by
  ext
  simp only [HomologicalComplex.comp_f, ChainComplex.single₀_map_f_zero]
  exact horseshoeComparisonMiddleComponent_zero_augmentation
    hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w

private noncomputable def horseshoeComparisonHom :
    HorseshoeData.Hom (H := H) (H' := H') (φ := φ) (u := u) (w := w) where
  hom := horseshoeComparisonMiddleHom
    hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w
  comm_i := horseshoeComparisonMiddleHom_comm_i
    hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w
  comm_p := horseshoeComparisonMiddleHom_comm_p
    hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w
  augmentation := horseshoeComparisonMiddleHom_augmentation
    hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w

private theorem horseshoeComparisonHom_spec :
    (horseshoeComparisonHom
      hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w).Spec
        (sH := sH) (sH' := sH') := by
  refine { middle_f := ?_ }
  intro n
  change
    (sH.middleXIso n).inv ≫
        horseshoeComparisonMiddleComponent
          hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n ≫
        (sH'.middleXIso n).hom =
      Biprod.ofComponents (u.hom.f n) 0
        (biprod.inr ≫
          ((sH.middleXIso n).inv ≫
            horseshoeComparisonMiddleComponent
              hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w n ≫
            (sH'.middleXIso n).hom) ≫ biprod.fst)
        (w.hom.f n)
  rw [horseshoeComparisonMiddleComponent_coordinate]
  unfold horseshoeComparisonMiddleMatrix
  simp

/-- In an abelian category `C`, take short exact sequences `S,S′`,
projective endpoint resolutions `P₁,P₃` and `P₁′,P₃′`, and
horseshoe resolutions `H,H′`. Given a sequence
map `φ`, endpoint maps `u,w`, and coordinate specifications
for `H,H′`, there exists a strict comparison with these endpoint
maps and the stated coordinate formula. -/
theorem HorseshoeData.nonempty_hom_spec :
    Nonempty { F : HorseshoeData.Hom
      (H := H) (H' := H') (φ := φ) (u := u) (w := w) //
      F.Spec (sH := sH) (sH' := sH') } := by
  exact ⟨⟨horseshoeComparisonHom
    hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w,
    horseshoeComparisonHom_spec
      hS hS' P₁ P₃ P₁' P₃' H H' sH sH' φ u w⟩⟩

include sH sH' in
/-- In an abelian category `C`, take short exact sequences `S,S′`,
projective endpoint resolutions `P₁,P₃` and `P₁′,P₃′`, and
horseshoe resolutions `H,H′`. Every map of the
short exact sequences and supplied endpoint projective-resolution
maps admit a strict comparison of `H` with `H′`. -/
theorem HorseshoeData.nonempty_hom :
    Nonempty (HorseshoeData.Hom
      (H := H) (H' := H') (φ := φ) (u := u) (w := w)) :=
  (HorseshoeData.nonempty_hom_spec
    (hS := hS) (hS' := hS') (P₁ := P₁) (P₃ := P₃)
    (P₁' := P₁') (P₃' := P₃') (H := H) (H' := H')
    (sH := sH) (sH' := sH') (φ := φ) (u := u) (w := w)).map Subtype.val

end CategoryTheory.ProjectiveResolution

end
