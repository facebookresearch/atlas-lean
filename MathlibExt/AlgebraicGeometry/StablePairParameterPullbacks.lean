/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StablePairFamilies

/-!
# Stable-pair parameter pullbacks and the fine-moduli universal property

Every parameter change is the literal map of products. Both the sheaf
and its section are pulled back by the native module functor. The
comparison maps are native pullbackComp, pullbackCongr and pullbackId.
The universal property quantifies over every parameter scheme and
actual family; it does not postulate a named family functor.

Reference: Pandharipande–Thomas, arXiv:0707.2348v5, §2.3, (2.9).
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StablePairParameterPullbacks

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open StablePairFamilies LineBundleTaskContracts
open AlgebraicBundleGeometry

variable {X T U V : Over (Spec (.of ℂ))}

/-- A projective parameter has an actual closed projective-bundle embedding. -/
structure ProjectiveParameter (P : Over (Spec (.of ℂ))) where
  dimension : ℕ
  space : ProjectiveBundle (Over.mk (𝟙 (Spec (.of ℂ)))) 0 dimension
    (SheafOfModules.free (R := (Spec (.of ℂ)).ringCatSheaf) (Fin (dimension+1)))
  embedding : P ⟶ space.total
  [closed : IsClosedImmersion embedding.left]
  [proper : IsProper P.hom]
  [noetherian : IsNoetherian P.left]

/-- The actual id_X × f on the fibre products. -/
def productMap (X : Over (Spec (.of ℂ))) (f : U ⟶ T) : total X U ⟶ total X T :=
  pullback.lift (pullback.fst X.hom U.hom)
    (pullback.snd X.hom U.hom ≫ f.left) (by
      simp only [Category.assoc, Over.w f]
      exact pullback.condition)

@[simp] theorem productMap_id (X T : Over (Spec (.of ℂ))) :
    productMap X (𝟙 T) = 𝟙 (total X T) := by
  apply pullback.hom_ext <;>
    simp only [productMap, Over.id_left, Category.comp_id, Category.id_comp,
      pullback.lift_fst, pullback.lift_snd]

@[simp] theorem productMap_comp (f : U ⟶ T) (g : V ⟶ U) :
    productMap X (g ≫ f) = productMap X g ≫ productMap X f := by
  apply pullback.hom_ext <;> simp [productMap, Category.assoc]

/-- The literal parameter pullback, including its original section. -/
def rawReindex (f : U ⟶ T) (F : RawPair X T) : RawPair X U where
  module := (Scheme.Modules.pullback (productMap X f)).obj F.module
  sectionMap := pullbackSection (productMap X f) F.sectionMap

/-- The fixed underlying identity comparison. -/
def identityModuleIso (F : RawPair X T) :
    (rawReindex (𝟙 T) F).module ≅ F.module :=
  (Scheme.Modules.pullbackCongr (productMap_id X T)).app F.module ≪≫
    (Scheme.Modules.pullbackId (total X T)).app F.module

/-- The fixed underlying iterated-pullback comparison. -/
def compositionModuleIso (f : U ⟶ T) (g : V ⟶ U) (F : RawPair X T) :
    (rawReindex g (rawReindex f F)).module ≅ (rawReindex (g ≫ f) F).module :=
  (Scheme.Modules.pullbackComp (productMap X g) (productMap X f)).app F.module ≪≫
    (Scheme.Modules.pullbackCongr (productMap_comp (X := X) f g).symm).app F.module

/-- Actual section-preserving isomorphisms, also usable before stability is proved. -/
structure RawIso (F G : RawPair X T) where
  iso : F.module ≅ G.module
  section_eq : F.sectionMap ≫ iso.hom = G.sectionMap

/-- Reindex the actual section-preserving pair arrow by the native module pullback. -/
def rawIsoReindex (f : U ⟶ T) {F G : RawPair X T} (e : RawIso F G) :
    RawIso (rawReindex f F) (rawReindex f G) := by
  refine ⟨(Scheme.Modules.pullback (productMap X f)).mapIso e.iso, ?_⟩
  change pullbackSection (productMap X f) F.sectionMap ≫
    (Scheme.Modules.pullback (productMap X f)).map e.iso.hom =
      pullbackSection (productMap X f) G.sectionMap
  dsimp only [LineBundleTaskContracts.pullbackSection]
  rw [Category.assoc, ← Functor.map_comp, e.section_eq]

/-- The precise family conditions needed after the fixed parameter pullback. -/
def ReindexIsFamily (f : U ⟶ T) (F : Family X T) : Prop :=
  coherent (rawReindex f F.toRawPair).module ∧
    FlatOver (projection X U) (rawReindex f F.toRawPair).module ∧
      ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ U.left),
        PureDimension (fibre (rawReindex f F.toRawPair) Ω p) 1 ∧
          supportDimension (cokernel (fibreSection (rawReindex f F.toRawPair) Ω p)) ≤ (0 : ℕ)

/-- Build the family from proofs of those actual pulled-back properties. -/
def reindexFamily (f : U ⟶ T) (F : Family X T) (h : ReindexIsFamily f F) : Family X U :=
  { rawReindex f F.toRawPair with coherent := h.1, flat := h.2.1, geometric := h.2.2 }

/-- The actual family-groupoid functor once pullback stability has been proved. -/
def reindexFunctor (f : U ⟶ T) (h : ∀ F : Family X T, ReindexIsFamily f F) :
    Family X T ⥤ Family X U where
  obj F := reindexFamily f F (h F)
  map e := by
    let a := rawIsoReindex f (⟨e.iso,e.section_eq⟩ : RawIso _ _)
    exact ⟨a.iso,a.section_eq⟩
  map_id F := by
    apply PairIso.ext
    change (Scheme.Modules.pullback (productMap X f)).map (𝟙 F.module) = 𝟙 _
    exact (Scheme.Modules.pullback (productMap X f)).map_id F.module
  map_comp e a := by
    apply PairIso.ext
    change (Scheme.Modules.pullback (productMap X f)).map (e.iso.hom ≫ a.iso.hom) =
      (Scheme.Modules.pullback (productMap X f)).map e.iso.hom ≫
        (Scheme.Modules.pullback (productMap X f)).map a.iso.hom
    exact (Scheme.Modules.pullback (productMap X f)).map_comp e.iso.hom a.iso.hom

/-- The full fine-moduli universal property of an actual universal pair.
Any numerical component is selected by applying this property to that
subfunctor of actual families. -/
def Represents (P : Over (Spec (.of ℂ))) (F : Family X P) : Prop :=
  ∀ (T : Over (Spec (.of ℂ))) (G : Family X T),
    ∃! f : T ⟶ P, Nonempty (RawIso (rawReindex f F.toRawPair) G.toRawPair)

/-- Geometric parameters retain their actual complex structure map. -/
def geometricParameter (Ω : Type) [Field Ω] [Algebra ℂ Ω] : Over (Spec (.of ℂ)) :=
  Over.mk (Spec.algebraMap ℂ Ω)

/-- The test family lies fibrewise in the actual universal family's image. -/
def FibrewiseInImage {P : Over (Spec (.of ℂ))} (F : Family X P) (G : Family X T) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℂ Ω]
    (p : geometricParameter Ω ⟶ T),
    ∃ q : geometricParameter Ω ⟶ P,
      Nonempty (RawIso (rawReindex p G.toRawPair) (rawReindex q F.toRawPair))

/-- Fine-moduli local completeness for the actual image, including numerical components.
This is the source's §4.1 test-family universal property, rather than
an assertion that any parameter scheme is a stable-pair moduli space. -/
def RepresentsImage {P : Over (Spec (.of ℂ))} (F : Family X P) : Prop :=
  ∀ (T : Over (Spec (.of ℂ))) (G : Family X T), FibrewiseInImage F G →
    ∃! f : T ⟶ P, Nonempty (RawIso (rawReindex f F.toRawPair) G.toRawPair)

end MathlibExt.AlgebraicGeometry.StablePairParameterPullbacks
