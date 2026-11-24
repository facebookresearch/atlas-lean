/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Topology.Sets.Opens
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Actual bordered spaces and real-parameter maps

A bordered space is an actual open subspace of its specified ambient
space; `BorderedSpace.HasLocallyCompactAmbient` records that the ambient
space is Hausdorff, locally compact and countable at infinity (weaker than
D'Agnolo--Kashiwara goodness). A morphism is a continuous map of the interiors whose graph
closure projects properly to the source ambient space. No extension to
an ambient map is required. In particular, addition is ordinary real
addition on the interiors of the two-point compactified line.

Source: D'Agnolo--Kashiwara1311.2374v2, Definitions3.2.1 and4.1.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BorderedRealSpaceModels

open _root_.CategoryTheory TopologicalSpace Set

/-- A raw bordered pair: an open subset of an ambient topological space. D'Agnolo--Kashiwara's
bordered spaces (Definition 3.2.1) are open embeddings of good spaces (Hausdorff, locally compact,
countable at infinity, finite flabby dimension); this structure records only the raw pair. -/
structure BorderedSpace where
  ambient : TopCat.{0}
  openSet : Opens ambient

/-- The ambient space is Hausdorff, locally compact and countable at infinity. This is weaker than
D'Agnolo--Kashiwara goodness of the bordered space: nothing is required of the interior, and finite
flabby dimension is not recorded. -/
class BorderedSpace.HasLocallyCompactAmbient (B : BorderedSpace) : Prop where
  [t2 : T2Space B.ambient]
  [locallyCompact : LocallyCompactSpace B.ambient]
  [sigmaCompact : SigmaCompactSpace B.ambient]

attribute [instance] BorderedSpace.HasLocallyCompactAmbient.t2
  BorderedSpace.HasLocallyCompactAmbient.locallyCompact
  BorderedSpace.HasLocallyCompactAmbient.sigmaCompact

abbrev BorderedSpace.interior (B : BorderedSpace) := TopCat.of B.openSet

def inclusion (B : BorderedSpace) : B.interior ⟶ B.ambient :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

def graphClosure (B C : BorderedSpace) (f : B.interior ⟶ C.interior) :
    Set (B.ambient × C.ambient) :=
  closure (Set.range (fun x : B.openSet => (x.val, (f x).val)))

def graphProjection (B C : BorderedSpace) (f : B.interior ⟶ C.interior) :
    graphClosure B C f → B.ambient := fun x => x.val.1

structure BorderedMap (B C : BorderedSpace) where
  map : B.interior ⟶ C.interior
  proper : IsProperMap (graphProjection B C map)

/-- Compact target compactifications give the source's graph-proper condition. -/
def compactTargetMap (B C : BorderedSpace) [CompactSpace C.ambient]
    (f : B.interior ⟶ C.interior) : BorderedMap B C where
  map := f
  proper := isProperMap_fst_of_compactSpace.restrict isClosed_closure

/-- Native two-point compactification, with the finite interval as its interior. -/
def infiniteReal : BorderedSpace :=
  ⟨TopCat.of EReal, ⟨Ioo (⊥ : EReal) ⊤, isOpen_Ioo⟩⟩

/-- The finite part is the actual real line with its usual order topology. -/
def realOrderIso : ℝ ≃o Ioo (⊥ : EReal) ⊤ where
  toFun x := ⟨(x : EReal), EReal.bot_lt_coe x, EReal.coe_lt_top x⟩
  invFun x := x.val.toReal
  left_inv x := EReal.toReal_coe x
  right_inv x := Subtype.ext (EReal.coe_toReal x.property.2.ne x.property.1.ne')
  map_rel_iff' := EReal.coe_le_coe_iff

def realHomeomorph : ℝ ≃ₜ Ioo (⊥ : EReal) ⊤ := realOrderIso.toHomeomorph

instance : CompactSpace infiniteReal.ambient := inferInstanceAs (CompactSpace EReal)

/-- The two-point compactified line is a compact Hausdorff ambient space. -/
instance : infiniteReal.HasLocallyCompactAmbient where
  t2 := inferInstanceAs (T2Space EReal)
  locallyCompact := inferInstanceAs (LocallyCompactSpace EReal)
  sigmaCompact := inferInstanceAs (SigmaCompactSpace EReal)

/-- Products retain both original ambient spaces and open inclusions. -/
def product (B C : BorderedSpace) : BorderedSpace :=
  ⟨TopCat.of (B.ambient × C.ambient),
    ⟨{p | p.1 ∈ B.openSet ∧ p.2 ∈ C.openSet}, B.openSet.isOpen.prod C.openSet.isOpen⟩⟩

/-- Products of bordered spaces with such ambient spaces have such an ambient space. -/
instance (B C : BorderedSpace) [B.HasLocallyCompactAmbient] [C.HasLocallyCompactAmbient] :
    (product B C).HasLocallyCompactAmbient where
  t2 := inferInstanceAs (T2Space (B.ambient × C.ambient))
  locallyCompact := inferInstanceAs (LocallyCompactSpace (B.ambient × C.ambient))
  sigmaCompact := inferInstanceAs (SigmaCompactSpace (B.ambient × C.ambient))

/-- Addition is evaluated only on the genuine finite real coordinates. -/
def realAddition : (product infiniteReal infiniteReal).interior ⟶ infiniteReal.interior :=
  TopCat.ofHom {
    toFun x := realHomeomorph
      (realHomeomorph.symm ⟨x.val.1, x.property.1⟩ +
        realHomeomorph.symm ⟨x.val.2, x.property.2⟩)
    continuous_toFun := by
      have hf : Continuous (fun x : {p : EReal × EReal |
          p.1 ∈ Ioo (⊥ : EReal) ⊤ ∧ p.2 ∈ Ioo (⊥ : EReal) ⊤} =>
          (⟨x.val.1, x.property.1⟩ : Ioo (⊥ : EReal) ⊤)) :=
        (continuous_fst.comp continuous_subtype_val).subtype_mk _
      have hg : Continuous (fun x : {p : EReal × EReal |
          p.1 ∈ Ioo (⊥ : EReal) ⊤ ∧ p.2 ∈ Ioo (⊥ : EReal) ⊤} =>
          (⟨x.val.2, x.property.2⟩ : Ioo (⊥ : EReal) ⊤)) :=
        (continuous_snd.comp continuous_subtype_val).subtype_mk _
      exact realHomeomorph.continuous.comp
        ((realHomeomorph.symm.continuous.comp hf).add
          (realHomeomorph.symm.continuous.comp hg)) }

/-- The source's sum morphism uses graph closure, without adding opposite infinities. -/
def realAdditionBordered : BorderedMap (product infiniteReal infiniteReal) infiniteReal :=
  compactTargetMap _ _ realAddition

/-- The same finite-coordinate interpretation gives real negation. -/
def realNegation : infiniteReal.interior ⟶ infiniteReal.interior :=
  TopCat.ofHom {
    toFun x := realHomeomorph (-realHomeomorph.symm x)
    continuous_toFun := realHomeomorph.continuous.comp realHomeomorph.symm.continuous.neg }

def realNegationBordered : BorderedMap infiniteReal infiniteReal :=
  compactTargetMap _ _ realNegation

end MathlibExt.AlgebraicGeometry.BorderedRealSpaceModels
