/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.FramingCylinderCofiber
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCofiber

/-!
# The actual framing cofiber and canonical zero-arrow homotopy cofiber

The common homotopy pushout retains the original framing cone, Q endpoint,
insertion, contraction and both quotient legs. The two weak comparisons
are earned from these source maps. The original Q counit then compares
with the canonical homotopy cofiber of the unchanged zero-target arrow.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u v

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.FramingCylinderHomotopyCofiber

open OrdinaryHoChosenPuppe

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (d : GeneratedFunctorialReplacements.Data (C := C)) (Z : C) (hZ : IsZero Z)

/-- The span retains the actual Q-to-zero map and original remaining framing insertion. -/
def coneSpan : C ⥤ WalkingSpan ⥤ C where
  obj X := span (toZero Z hZ (d.Q.obj X)) ((FramingCylinderCone.inclusion d Z hZ).app X)
  map f := spanHomMk (d.Q.map f) (𝟙 Z) ((FramingCylinderCone.cone d Z hZ).map f)
    (hZ.isTerminal.hom_ext _ _) ((FramingCylinderCone.inclusion d Z hZ).naturality f).symm
  map_id X := by ext j; rcases j with (_ | _ | _) <;> simp
  map_comp f g := by ext j; rcases j with (_ | _ | _) <;> simp

/-- The original remaining cofiber carries both original span legs. -/
def spanCocone (X : C) :
    PushoutCocone (toZero Z hZ (d.Q.obj X)) ((FramingCylinderCone.inclusion d Z hZ).app X) :=
  PushoutCocone.mk (FramingCylinderCofiber.cofiberZero d Z hZ X)
    (FramingCylinderCofiber.cofiberLeg d Z hZ X) pushout.condition.symm

/-- The full span universal property is the original remaining pushout with its legs exchanged. -/
def spanIsColimit (X : C) : IsColimit (spanCocone d Z hZ X) :=
  (IsPushout.of_hasPushout ((FramingCylinderCone.inclusion d Z hZ).app X)
    (toZero Z hZ (d.Q.obj X))).flip.isColimit

/-- The span colimit computes the same actual framing cofiber. -/
def spanColimitIso (X : C) : (coneSpan d Z hZ ⋙ colim).obj X ≅
    (FramingCylinderCofiber.cofiber d Z hZ).obj X :=
  (colimit.isColimit ((coneSpan d Z hZ).obj X)).coconePointUniqueUpToIso (spanIsColimit d Z hZ X)

/-- The colimit comparison keeps the unchanged actual zero quotient leg. -/
theorem spanColimitIso_zero (X : C) :
    colimit.ι ((coneSpan d Z hZ).obj X) WalkingSpan.left ≫ (spanColimitIso d Z hZ X).hom =
      FramingCylinderCofiber.cofiberZero d Z hZ X :=
  (colimit.isColimit ((coneSpan d Z hZ).obj X)).fac (spanCocone d Z hZ X) WalkingSpan.left

/-- The colimit comparison keeps the whole original cone quotient leg. -/
theorem spanColimitIso_cone (X : C) :
    colimit.ι ((coneSpan d Z hZ).obj X) WalkingSpan.right ≫ (spanColimitIso d Z hZ X).hom =
      FramingCylinderCofiber.cofiberLeg d Z hZ X :=
  (colimit.isColimit ((coneSpan d Z hZ).obj X)).fac (spanCocone d Z hZ X) WalkingSpan.right

/-- Both original quotient legs give the whole natural span-colimit comparison. -/
def spanComparison : coneSpan d Z hZ ⋙ colim ≅ FramingCylinderCofiber.cofiber d Z hZ :=
  NatIso.ofComponents (spanColimitIso d Z hZ) (fun {X Y} f => by
    apply PushoutCocone.IsColimit.hom_ext (colimit.isColimit ((coneSpan d Z hZ).obj X))
    · exact hZ.isInitial.hom_ext _ _
    · change colimit.ι ((coneSpan d Z hZ).obj X) WalkingSpan.right ≫
          (colimMap ((coneSpan d Z hZ).map f) ≫ (spanColimitIso d Z hZ Y).hom) =
        colimit.ι ((coneSpan d Z hZ).obj X) WalkingSpan.right ≫
          ((spanColimitIso d Z hZ X).hom ≫ (FramingCylinderCofiber.cofiber d Z hZ).map f)
      rw [← Category.assoc, ι_colimMap, Category.assoc, spanColimitIso_cone,
        ← Category.assoc, spanColimitIso_cone]
      exact (FramingCylinderCofiber.cofiberLeg_naturality d Z hZ f).symm)

/-- The actual framing contraction followed by the original zero-to-terminal isomorphism. -/
def toTerminal (X : C) : (FramingCylinderCone.cone d Z hZ).obj X ⟶ ⊤_ C :=
  (FramingCylinderCone.contraction d Z hZ).app X ≫
    (hZ.isTerminal.uniqueUpToIso terminalIsTerminal).hom

/-- The terminal comparison is weak by the earned original framing contraction. -/
theorem toTerminal_weak (X : C) : weakEquivalences C (toTerminal d Z hZ X) :=
  (weakEquivalences C).comp_mem _ _ (FramingCylinderCone.contraction_weak d Z hZ X)
    (mem_weakEquivalences (hZ.isTerminal.uniqueUpToIso terminalIsTerminal).hom)

/-- The framing span maps naturally to the canonical cofiber span at the same Q endpoint. -/
def spanToCanonical : coneSpan d Z hZ ⟶ d.Q ⋙ zeroArrowFunctor Z hZ ⋙ cofiberSpan (C := C) where
  app X := spanHomMk (𝟙 (d.Q.obj X)) (𝟙 Z) (toTerminal d Z hZ X)
    (hZ.isTerminal.hom_ext _ _) (terminal.hom_ext _ _)
  naturality X Y f := by
    ext j
    rcases j with (_ | _ | _)
    · change d.Q.map f ≫ 𝟙 _ = 𝟙 _ ≫ d.Q.map f
      simp
    · exact hZ.isInitial.hom_ext _ _
    · exact terminal.hom_ext _ _

/-- The original q_X counit compares the full Q-zero arrow to the unchanged zero arrow. -/
def zeroQComparison : d.Q ⋙ zeroArrowFunctor Z hZ ⟶ zeroArrowFunctor Z hZ where
  app X := Arrow.homMk (d.q.app X) (𝟙 Z) (hZ.isTerminal.hom_ext _ _)
  naturality _ _ f := by
    apply Arrow.hom_ext
    · exact d.q.naturality f
    · exact hZ.isInitial.hom_ext _ _

section Canonical

variable [HasFunctorialFactorization (cofibrations C) (trivialFibrations C)]

/-- Homotopy pushout of the actual framing cone span. -/
def common : C ⥤ C := coneSpan d Z hZ ⋙ homotopyPushout

/-- The original homotopy-pushout comparison retains both actual framing cofiber legs. -/
def toFraming : common d Z hZ ⟶ FramingCylinderCofiber.cofiber d Z hZ :=
  Functor.whiskerLeft (coneSpan d Z hZ) (homotopyPushoutComparison (C := C)) ≫
    (spanComparison d Z hZ).hom

/-- The original framing contraction gives the canonical cofiber at the same Q endpoint. -/
def toCanonicalQ : common d Z hZ ⟶ d.Q ⋙ zeroArrowFunctor Z hZ ⋙ homotopyCofiber (C := C) :=
  Functor.whiskerRight (spanToCanonical d Z hZ) (homotopyPushout (C := C))

/-- Both original q_X and zero-identity maps give the canonical original-arrow comparison. -/
def canonicalQComparison :
    d.Q ⋙ zeroArrowFunctor Z hZ ⋙ homotopyCofiber (C := C) ⟶
      zeroArrowFunctor Z hZ ⋙ homotopyCofiber (C := C) :=
  Functor.whiskerRight (zeroQComparison d Z hZ) (homotopyCofiber (C := C))

/-- The complete canonical comparison retains the original framing contraction and q_X counit. -/
def toCanonical : common d Z hZ ⟶ zeroArrowFunctor Z hZ ⋙ homotopyCofiber (C := C) :=
  toCanonicalQ d Z hZ ≫ canonicalQComparison d Z hZ

/-- The framing comparison is weak from the actual remaining insertion and Q/zero cofibrancy. -/
theorem toFraming_weak (X : C) : weakEquivalences C ((toFraming d Z hZ).app X) := by
  let _ : IsCofibrant (((coneSpan d Z hZ).obj X).obj WalkingSpan.zero) := d.q_cofibrant X
  let _ : IsCofibrant (((coneSpan d Z hZ).obj X).obj WalkingSpan.left) :=
    (isCofibrant_iff_of_isInitial (𝟙 Z) hZ.isInitial).mpr (by infer_instance)
  let _ : Cofibration (((coneSpan d Z hZ).obj X).map WalkingSpan.Hom.snd) :=
    (cofibration_iff _).mpr (FramingCylinderCone.inclusion_cofibration d Z hZ X)
  exact (weakEquivalences C).comp_mem _ _
    ((weakEquivalence_iff _).mp
      (weakEquivalence_homotopyPushoutComparison_of_snd ((coneSpan d Z hZ).obj X)))
    (mem_weakEquivalences (spanColimitIso d Z hZ X).hom)

/-- The map to the Q canonical cofiber is weak by the earned framing contraction. -/
theorem toCanonicalQ_weak (X : C) : weakEquivalences C ((toCanonicalQ d Z hZ).app X) := by
  apply (weakEquivalence_iff _).mp
  apply homotopyPushout_map_weakEquivalence ((spanToCanonical d Z hZ).app X)
  intro j
  rcases j with (_ | _ | _)
  · change WeakEquivalence (𝟙 (d.Q.obj X))
    infer_instance
  · change WeakEquivalence (𝟙 Z)
    infer_instance
  · change WeakEquivalence (toTerminal d Z hZ X)
    exact (weakEquivalence_iff _).mpr (toTerminal_weak d Z hZ X)

/-- The original q_X counit gives a weak map of canonical homotopy cofibers. -/
theorem canonicalQComparison_weak (X : C) :
    weakEquivalences C ((canonicalQComparison d Z hZ).app X) :=
  (weakEquivalence_iff _).mp
    (homotopyCofiber_map_weakEquivalence ((zeroQComparison d Z hZ).app X)
      ((weakEquivalence_iff _).mpr (d.q_trivialFibration X).2)
      (by change WeakEquivalence (𝟙 Z); infer_instance))

/-- Every complete comparison to the canonical original-arrow cofiber is weak. -/
theorem toCanonical_weak (X : C) : weakEquivalences C ((toCanonical d Z hZ).app X) :=
  (weakEquivalences C).comp_mem _ _ (toCanonicalQ_weak d Z hZ X)
    (canonicalQComparison_weak d Z hZ X)

/-- The original source weak map gives a full natural isomorphism to the framing cofiber in Ho. -/
def framingHoIso : common d Z hZ ⋙ toHomotopyCategory C ≅
    FramingCylinderCofiber.cofiber d Z hZ ⋙ toHomotopyCategory C := by
  letI (X : C) : IsIso ((toHomotopyCategory C).map ((toFraming d Z hZ).app X)) :=
    Localization.inverts (toHomotopyCategory C) (weakEquivalences C) _ (toFraming_weak d Z hZ X)
  exact NatIso.ofComponents (fun X => asIso ((toHomotopyCategory C).map ((toFraming d Z hZ).app X)))
    (fun {X Y} f => by
      change (toHomotopyCategory C).map ((common d Z hZ).map f) ≫
          (toHomotopyCategory C).map ((toFraming d Z hZ).app Y) =
        (toHomotopyCategory C).map ((toFraming d Z hZ).app X) ≫
          (toHomotopyCategory C).map ((FramingCylinderCofiber.cofiber d Z hZ).map f)
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact (toHomotopyCategory C).congr_map ((toFraming d Z hZ).naturality f))

/-- The same original source maps give the full natural canonical-cofiber comparison in Ho. -/
def canonicalHoIso : common d Z hZ ⋙ toHomotopyCategory C ≅
    zeroArrowFunctor Z hZ ⋙ homotopyCofiber (C := C) ⋙ toHomotopyCategory C := by
  letI (X : C) : IsIso ((toHomotopyCategory C).map ((toCanonical d Z hZ).app X)) :=
    Localization.inverts (toHomotopyCategory C) (weakEquivalences C) _ (toCanonical_weak d Z hZ X)
  exact NatIso.ofComponents (fun X => asIso ((toHomotopyCategory C).map ((toCanonical d Z hZ).app X)))
    (fun {X Y} f => by
      change (toHomotopyCategory C).map ((common d Z hZ).map f) ≫
          (toHomotopyCategory C).map ((toCanonical d Z hZ).app Y) =
        (toHomotopyCategory C).map ((toCanonical d Z hZ).app X) ≫
          (toHomotopyCategory C).map ((zeroArrowFunctor Z hZ ⋙ homotopyCofiber (C := C)).map f)
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact (toHomotopyCategory C).congr_map ((toCanonical d Z hZ).naturality f))

/-- The actual framing cofiber computes the same canonical homotopy cofiber naturally. -/
def comparison : FramingCylinderCofiber.cofiber d Z hZ ⋙ toHomotopyCategory C ≅
    zeroArrowFunctor Z hZ ⋙ homotopyCofiber (C := C) ⋙ toHomotopyCategory C :=
  (framingHoIso d Z hZ).symm ≪≫ canonicalHoIso d Z hZ

end Canonical

end HomotopicalAlgebra.FramingCylinderHomotopyCofiber
