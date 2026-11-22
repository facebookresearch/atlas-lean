/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedOrdinaryCofiber
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCofiber

/-!
# Original cone cofibers and the canonical homotopy cofiber

The span retains the original input arrow and I insertion. Its ordinary
colimit is compared with the same chosen Puppe pushout on both original
legs. The actual contraction gives a natural map to the canonical zero
span. Homotopy pushout and the original Q counit then compare these
constructions with the existing canonical homotopy cofiber.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe w u v

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.GeneratedOrdinaryCofiberComparison

open GeneratedOrdinaryCofiber

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z)

/-- The original contraction followed by the unique zero-to-terminal isomorphism. -/
def coneToTerminal (X : C) : (GeneratedOrdinaryCone.cone d Z hZ).obj X ⟶ ⊤_ C :=
  (GeneratedOrdinaryCone.contraction d Z hZ).app X ≫
    (hZ.isTerminal.uniqueUpToIso terminalIsTerminal).hom

/-- The terminal comparison retains the original contraction as its first factor. -/
theorem coneToTerminal_weak (X : C) : weakEquivalences C (coneToTerminal d Z hZ X) :=
  (weakEquivalences C).comp_mem _ _ (GeneratedOrdinaryCone.contraction_weak d Z hZ X)
    (mem_weakEquivalences (hZ.isTerminal.uniqueUpToIso terminalIsTerminal).hom)

/-- The canonical terminal endpoint agrees with that complete original factor map. -/
theorem coneToTerminal_eq (X : C) :
    coneToTerminal d Z hZ X = terminal.from ((GeneratedOrdinaryCone.cone d Z hZ).obj X) :=
  terminal.hom_ext _ _

/-- The original cofiber span has the input target on the left and the I cone on the right. -/
def coneSpan : Arrow C ⥤ (WalkingSpan ⥤ C) where
  obj F := span F.hom ((GeneratedOrdinaryCone.inclusion d Z hZ).app F.left)
  map a := spanHomMk a.left a.right ((GeneratedOrdinaryCone.cone d Z hZ).map a.left)
    a.w.symm ((GeneratedOrdinaryCone.inclusion d Z hZ).naturality a.left).symm
  map_id F := by
    ext j
    rcases j with (_ | _ | _) <;> simp
  map_comp a b := by
    ext j
    rcases j with (_ | _ | _) <;> simp

/-- This cocone exchanges the two original chosen pushout legs. -/
def coneSpanCocone (F : Arrow C) :
    PushoutCocone F.hom ((GeneratedOrdinaryCone.inclusion d Z hZ).app F.left) :=
  PushoutCocone.mk (GeneratedOrdinaryCone.cofiberCocone d Z hZ F).inr
    (GeneratedOrdinaryCone.cofiberCocone d Z hZ F).inl
    (GeneratedOrdinaryCone.cofiberCocone d Z hZ F).condition.symm

/-- The full colimit witness is the flipped original pushout witness. -/
def coneSpanIsColimit (F : Arrow C) : IsColimit (coneSpanCocone d Z hZ F) :=
  (IsPushout.of_isColimit (GeneratedOrdinaryCone.cofiberIsColimit d Z hZ F)).flip.isColimit

/-- The canonical span colimit and the original Puppe cofiber have the same universal property. -/
def coneSpanColimitIso (F : Arrow C) :
    (coneSpan d Z hZ ⋙ colim).obj F ≅ (cofiber d Z hZ).obj F :=
  (colimit.isColimit ((coneSpan d Z hZ).obj F)).coconePointUniqueUpToIso
    (coneSpanIsColimit d Z hZ F)

/-- The comparison keeps the complete original target leg. -/
theorem coneSpanColimitIso_target (F : Arrow C) :
    colimit.ι ((coneSpan d Z hZ).obj F) WalkingSpan.left ≫
        (coneSpanColimitIso d Z hZ F).hom =
      (GeneratedOrdinaryCone.cofiberCocone d Z hZ F).inr :=
  (colimit.isColimit ((coneSpan d Z hZ).obj F)).fac (coneSpanCocone d Z hZ F) WalkingSpan.left

/-- The comparison keeps the complete original cone leg. -/
theorem coneSpanColimitIso_cone (F : Arrow C) :
    colimit.ι ((coneSpan d Z hZ).obj F) WalkingSpan.right ≫
        (coneSpanColimitIso d Z hZ F).hom =
      (GeneratedOrdinaryCone.cofiberCocone d Z hZ F).inl :=
  (colimit.isColimit ((coneSpan d Z hZ).obj F)).fac (coneSpanCocone d Z hZ F) WalkingSpan.right

/-- Both actual pushout legs give the whole natural span-colimit comparison. -/
def coneSpanComparison : coneSpan d Z hZ ⋙ colim ≅ cofiber d Z hZ :=
  NatIso.ofComponents (coneSpanColimitIso d Z hZ) (fun {F G} a => by
    apply PushoutCocone.IsColimit.hom_ext (colimit.isColimit ((coneSpan d Z hZ).obj F))
    · change colimit.ι ((coneSpan d Z hZ).obj F) WalkingSpan.left ≫
          (colimMap ((coneSpan d Z hZ).map a) ≫ (coneSpanColimitIso d Z hZ G).hom) =
        colimit.ι ((coneSpan d Z hZ).obj F) WalkingSpan.left ≫
          ((coneSpanColimitIso d Z hZ F).hom ≫ (cofiber d Z hZ).map a)
      rw [← Category.assoc, ι_colimMap, Category.assoc, coneSpanColimitIso_target,
        ← Category.assoc, coneSpanColimitIso_target]
      exact (OrdinaryHoChosenPuppe.cofiberMap_target (GeneratedOrdinaryCone.cone d Z hZ)
        (GeneratedOrdinaryCone.inclusion d Z hZ)
        (GeneratedOrdinaryCone.cofiberCocone d Z hZ)
        (GeneratedOrdinaryCone.cofiberIsColimit d Z hZ) a).symm
    · change colimit.ι ((coneSpan d Z hZ).obj F) WalkingSpan.right ≫
          (colimMap ((coneSpan d Z hZ).map a) ≫ (coneSpanColimitIso d Z hZ G).hom) =
        colimit.ι ((coneSpan d Z hZ).obj F) WalkingSpan.right ≫
          ((coneSpanColimitIso d Z hZ F).hom ≫ (cofiber d Z hZ).map a)
      rw [← Category.assoc, ι_colimMap, Category.assoc, coneSpanColimitIso_cone,
        ← Category.assoc, coneSpanColimitIso_cone]
      exact (OrdinaryHoChosenPuppe.cofiberMap_cone (GeneratedOrdinaryCone.cone d Z hZ)
        (GeneratedOrdinaryCone.inclusion d Z hZ)
        (GeneratedOrdinaryCone.cofiberCocone d Z hZ)
        (GeneratedOrdinaryCone.cofiberIsColimit d Z hZ) a).symm)

/-- Collapse only the actual cone component to the canonical terminal endpoint. -/
def coneToCofiberSpan : coneSpan d Z hZ ⟶ cofiberSpan (C := C) where
  app F := spanHomMk (𝟙 F.left) (𝟙 F.right) (coneToTerminal d Z hZ F.left)
    (by
      change F.hom ≫ 𝟙 F.right = 𝟙 F.left ≫ F.hom
      simp) (terminal.hom_ext _ _)
  naturality F G a := by
    ext j
    rcases j with (_ | _ | _)
    · change a.left ≫ 𝟙 G.left = 𝟙 F.left ≫ a.left
      simp
    · change a.right ≫ 𝟙 G.right = 𝟙 F.right ≫ a.right
      simp
    · exact terminal.hom_ext _ _

section Canonical

variable [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]

/-- Homotopy pushout of the unchanged original cone span. -/
def coneHomotopy : Arrow C ⥤ C := coneSpan d Z hZ ⋙ homotopyPushout

/-- The canonical homotopy-pushout comparison followed by the original two-leg isomorphism. -/
def coneHomotopyToCofiber : coneHomotopy d Z hZ ⟶ cofiber d Z hZ :=
  Functor.whiskerLeft (coneSpan d Z hZ) (homotopyPushoutComparison (C := C)) ≫
    (coneSpanComparison d Z hZ).hom

/-- Homotopy pushout carries the actual cone contraction to the canonical cofiber. -/
def coneHomotopyToCanonical : coneHomotopy d Z hZ ⟶ homotopyCofiber (C := C) :=
  Functor.whiskerRight (coneToCofiberSpan d Z hZ) (homotopyPushout (C := C))

/-- The map to the original cofiber is weak at the actual cofibrant span endpoints. -/
theorem coneHomotopyToCofiber_weak (F : Arrow C)
    [IsCofibrant F.left] [IsCofibrant F.right] :
    weakEquivalences C ((coneHomotopyToCofiber d Z hZ).app F) := by
  let _ : IsCofibrant (((coneSpan d Z hZ).obj F).obj WalkingSpan.zero) :=
    inferInstanceAs (IsCofibrant F.left)
  let _ : IsCofibrant (((coneSpan d Z hZ).obj F).obj WalkingSpan.left) :=
    inferInstanceAs (IsCofibrant F.right)
  let _ : Cofibration (((coneSpan d Z hZ).obj F).map WalkingSpan.Hom.snd) :=
    (cofibration_iff _).mpr (GeneratedOrdinaryCone.inclusion_cofibration d Z hZ F.left)
  exact (weakEquivalences C).comp_mem _ _
    ((weakEquivalence_iff _).mp
      (weakEquivalence_homotopyPushoutComparison_of_snd ((coneSpan d Z hZ).obj F)))
    (mem_weakEquivalences (coneSpanColimitIso d Z hZ F).hom)

/-- The map to the canonical cofiber is weak by the original cone contraction in every input. -/
theorem coneHomotopyToCanonical_weak (F : Arrow C) :
    weakEquivalences C ((coneHomotopyToCanonical d Z hZ).app F) := by
  apply (weakEquivalence_iff _).mp
  apply homotopyPushout_map_weakEquivalence ((coneToCofiberSpan d Z hZ).app F)
  intro j
  rcases j with (_ | _ | _)
  · change WeakEquivalence (𝟙 F.left)
    infer_instance
  · change WeakEquivalence (𝟙 F.right)
    infer_instance
  · change WeakEquivalence (coneToTerminal d Z hZ F.left)
    exact (weakEquivalence_iff _).mpr (coneToTerminal_weak d Z hZ F.left)

/-- The canonical cofiber of the Q-image retains its original counit comparison. -/
def canonicalReplacementComparison :
    replacementArrow d ⋙ homotopyCofiber (C := C) ⟶ homotopyCofiber (C := C) :=
  Functor.whiskerRight (replacementArrowCounit d) (homotopyCofiber (C := C))

/-- The two original Q counits prove weakness of the whole canonical cofiber comparison. -/
theorem canonicalReplacementComparison_weak (F : Arrow C) :
    weakEquivalences C ((canonicalReplacementComparison d).app F) :=
  (weakEquivalence_iff _).mp
    (homotopyCofiber_map_weakEquivalence ((replacementArrowCounit d).app F)
      ((weakEquivalence_iff _).mpr (GeneratedFunctorialReplacements.counit_weak d F.left))
      ((weakEquivalence_iff _).mpr (GeneratedFunctorialReplacements.counit_weak d F.right)))

/-- The common homotopy cofiber uses the complete original Q-image cone span. -/
def coneQHomotopy : Arrow C ⥤ C := replacementArrow d ⋙ coneHomotopy d Z hZ

/-- Its original span comparison has the generated Puppe cofiber as target. -/
def coneQToGenerated : coneQHomotopy d Z hZ ⟶ derivedCofiber d Z hZ :=
  Functor.whiskerLeft (replacementArrow d) (coneHomotopyToCofiber d Z hZ)

/-- Its canonical comparison retains the actual cone collapse and both original Q counits. -/
def coneQToCanonical : coneQHomotopy d Z hZ ⟶ homotopyCofiber (C := C) :=
  Functor.whiskerLeft (replacementArrow d) (coneHomotopyToCanonical d Z hZ) ≫
    canonicalReplacementComparison d

/-- Original Q endpoint cofibrancy proves weakness of the common-source Puppe comparison. -/
theorem coneQToGenerated_weak (F : Arrow C) :
    weakEquivalences C ((coneQToGenerated d Z hZ).app F) := by
  let _ : IsCofibrant ((replacementArrow d).obj F).left :=
    GeneratedFunctorialReplacements.Q_isCofibrant d F.left
  let _ : IsCofibrant ((replacementArrow d).obj F).right :=
    GeneratedFunctorialReplacements.Q_isCofibrant d F.right
  exact coneHomotopyToCofiber_weak d Z hZ ((replacementArrow d).obj F)

/-- Both actual common-source maps into the canonical cofiber are weak. -/
theorem coneQToCanonical_weak (F : Arrow C) :
    weakEquivalences C ((coneQToCanonical d Z hZ).app F) :=
  (weakEquivalences C).comp_mem _ _
    (coneHomotopyToCanonical_weak d Z hZ ((replacementArrow d).obj F))
    (canonicalReplacementComparison_weak d F)

/-- The actual weak comparison to the Puppe cofiber gives a full natural isomorphism in ordinary Ho. -/
def generatedHoIso :
    coneQHomotopy d Z hZ ⋙ toHomotopyCategory C ≅
      derivedCofiber d Z hZ ⋙ toHomotopyCategory C := by
  letI (F : Arrow C) : IsIso
      ((toHomotopyCategory C).map ((coneQToGenerated d Z hZ).app F)) :=
    Localization.inverts (toHomotopyCategory C) (weakEquivalences C) _
      (coneQToGenerated_weak d Z hZ F)
  exact NatIso.ofComponents
    (fun F => asIso ((toHomotopyCategory C).map ((coneQToGenerated d Z hZ).app F)))
    (fun {F G} a => by
      change (toHomotopyCategory C).map ((coneQHomotopy d Z hZ).map a) ≫
          (toHomotopyCategory C).map ((coneQToGenerated d Z hZ).app G) =
        (toHomotopyCategory C).map ((coneQToGenerated d Z hZ).app F) ≫
          (toHomotopyCategory C).map ((derivedCofiber d Z hZ).map a)
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact (toHomotopyCategory C).congr_map ((coneQToGenerated d Z hZ).naturality a))

/-- The original cone and Q maps give a full natural isomorphism to the canonical cofiber in Ho. -/
def canonicalHoIso :
    coneQHomotopy d Z hZ ⋙ toHomotopyCategory C ≅
      homotopyCofiber (C := C) ⋙ toHomotopyCategory C := by
  letI (F : Arrow C) : IsIso
      ((toHomotopyCategory C).map ((coneQToCanonical d Z hZ).app F)) :=
    Localization.inverts (toHomotopyCategory C) (weakEquivalences C) _
      (coneQToCanonical_weak d Z hZ F)
  exact NatIso.ofComponents
    (fun F => asIso ((toHomotopyCategory C).map ((coneQToCanonical d Z hZ).app F)))
    (fun {F G} a => by
      change (toHomotopyCategory C).map ((coneQHomotopy d Z hZ).map a) ≫
          (toHomotopyCategory C).map ((coneQToCanonical d Z hZ).app G) =
        (toHomotopyCategory C).map ((coneQToCanonical d Z hZ).app F) ≫
          (toHomotopyCategory C).map ((homotopyCofiber (C := C)).map a)
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact (toHomotopyCategory C).congr_map ((coneQToCanonical d Z hZ).naturality a))

/-- The original generated Puppe cofiber computes the same canonical homotopy cofiber naturally. -/
def comparison : derivedCofiber d Z hZ ⋙ toHomotopyCategory C ≅
    homotopyCofiber (C := C) ⋙ toHomotopyCategory C :=
  (generatedHoIso d Z hZ).symm ≪≫ canonicalHoIso d Z hZ

end Canonical

/-- Conventional generation supplies the actual factorization hypothesis of the canonical cofiber. -/
def canonicalCofiberOfGeneration : Arrow C ⥤ C := by
  letI := d.hasFunctorialFactorizationCofibrationsTrivialFibrations
  exact homotopyCofiber (C := C)

/-- The full ordinary comparison needs only the original generation, rank and chosen zero. -/
def comparisonOfGeneration : derivedCofiber d Z hZ ⋙ toHomotopyCategory C ≅
    canonicalCofiberOfGeneration d ⋙ toHomotopyCategory C := by
  letI := d.hasFunctorialFactorizationCofibrationsTrivialFibrations
  exact comparison d Z hZ

end HomotopicalAlgebra.GeneratedOrdinaryCofiberComparison
