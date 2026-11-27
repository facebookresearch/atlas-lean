/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridFiberDegreeZero
public import MathlibExt.KTheory.Exact.Quillen.QuillenSpanFlagEndpointComposition
public import MathlibExt.KTheory.Exact.Quillen.SpanFlagStageShellNormalized
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageZeroRowReconstruction

/-!
# Connectedness of all strict Quillen Stage-grid fibers

Two lifts of one retained Quillen simplex have canonically comparable material
zero rows.  Exact lifts of the comparison on Quillen vertices determine
endpoint-compatible comparisons of every Stage shell.  Ordered shell
composition controls the upper half of the zero row, while the unique material
kernel comparisons control the lower half.  The resulting zero-row natural
isomorphism extends to the whole Stage and gives a direct morphism in the
strict fiber.

This file proves categorical connectedness and the resulting theorem-valued
finality and initiality statements only.  It installs no connectedness,
finality, or initiality instance and makes no fiber contractibility,
realization weak-equivalence, or Q/S comparison claim.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

local instance quillenStageGridFiberConnectedWaldhausenCategory :
    WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

namespace QuillenStageGridFiberComparison

variable {a : SimplexCategory} {q : QuillenQSimplex C a}
variable (X Y : QuillenStageGridFiber q)

/-- Equality of the two retained simplices, extracted from the strict-fiber
equalities. -/
theorem retainedEq : X.1.q = Y.1.q :=
  (congrArg Discrete.as X.2).trans (congrArg Discrete.as Y.2).symm

/-- The corresponding isomorphism in the discrete retained-simplex category. -/
@[no_expose]
def retainedDiscreteIso : Discrete.mk X.1.q ≅ Discrete.mk Y.1.q :=
  eqToIso (Discrete.ext (retainedEq X Y))

/-- The retained-simplex isomorphism after forgetting discreteness. -/
@[no_expose]
def retainedIso : X.1.q ≅ Y.1.q :=
  (quillenQSimplexDiscreteInclusion C a).mapIso (retainedDiscreteIso X Y)

/-- Exact comparison between the Quillen simplices extracted from the two
material grids. -/
@[no_expose]
def extractedIso :
    (edgewiseStageQuillenSimplexFunctor C a).obj X.1.grid ≅
      (edgewiseStageQuillenSimplexFunctor C a).obj Y.1.grid :=
  X.1.agreementIso.trans ((retainedIso X Y).trans Y.1.agreementIso.symm)

/-- The exact-category isomorphism selected over one component of the
extracted Quillen-simplex comparison. -/
@[no_expose]
noncomputable def vertexLift (k : Fin (a.len + 1)) :
    { e : edgewiseStageVertex X.1.grid.obj k ≅
        edgewiseStageVertex Y.1.grid.obj k //
      QuillenQ.underlyingIso e = (extractedIso X Y).app k } :=
  Classical.choice
    (quillenQ_iso_lifts_to_underlying_iso_eq ((extractedIso X Y).app k))

/-- Underlying exact-category isomorphism at one extracted vertex. -/
@[no_expose]
noncomputable def vertexIso (k : Fin (a.len + 1)) :
    edgewiseStageVertex X.1.grid.obj k ≅
      edgewiseStageVertex Y.1.grid.obj k :=
  (vertexLift X Y k).1

@[simp]
theorem vertexIso_underlyingIso (k : Fin (a.len + 1)) :
    QuillenQ.underlyingIso (vertexIso X Y k) =
      (extractedIso X Y).app k :=
  (vertexLift X Y k).2

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the extracted comparison, written using the selected exact
vertex isomorphisms and normalized raw shell representatives. -/
theorem normalizedShell_naturality
    {k l : Fin (a.len + 1)} (hkl : k ≤ l) :
    QuillenQ.mkHom
          (edgewiseStageShellSpanNormalized X.1.grid.obj k l hkl) ≫
        (QuillenQ.underlyingIso (vertexIso X Y l)).hom =
      (QuillenQ.underlyingIso (vertexIso X Y k)).hom ≫
        QuillenQ.mkHom
          (edgewiseStageShellSpanNormalized Y.1.grid.obj k l hkl) := by
  have hvk := congrArg Iso.hom (vertexIso_underlyingIso X Y k)
  have hvl := congrArg Iso.hom (vertexIso_underlyingIso X Y l)
  have hNX := edgewiseStageShellSpanNormalized_mkHom
    (C := C) X.1.grid.obj k l hkl
  have hNY := edgewiseStageShellSpanNormalized_mkHom
    (C := C) Y.1.grid.obj k l hkl
  rw [hNY, hNX]
  rw [hvl, hvk]
  exact (extractedIso X Y).hom.naturality (homOfLE hkl)

/-- Endpoint-compatible comparison of the normalized raw shell spans. -/
@[no_expose]
noncomputable def normalizedShellEndpointIso
    {k l : Fin (a.len + 1)} (hkl : k ≤ l) :
    QuillenSpan.EndpointIso
      (edgewiseStageShellSpanNormalized X.1.grid.obj k l hkl)
      (edgewiseStageShellSpanNormalized Y.1.grid.obj k l hkl)
      (vertexIso X Y k) (vertexIso X Y l) :=
  QuillenQ.endpointIsoOfMkHomNaturality _ _ _ _
    (normalizedShell_naturality X Y hkl)

/-- The raw shell comparison with its source endpoint transported to the
fixed cross vertex. -/
@[no_expose]
def rawToNormalizedEndpointIso
    (A : Stage C (edgewiseQ.obj a).len)
    {k l : Fin (a.len + 1)} (hkl : k ≤ l) :
    QuillenSpan.EndpointIso
      (edgewiseStageShellPacket A k l hkl).span
      (edgewiseStageShellSpanNormalized A k l hkl)
      (eqToIso (edgewiseStageShellSourceEqVertex A k l hkl))
      (eqToIso (edgewiseStageShellTargetEqVertex A k l hkl)) :=
  ⟨Iso.refl _, by simp, by simp⟩

/-- Raw source-endpoint comparison induced by the selected vertex iso. -/
@[no_expose]
noncomputable def shellSourceIso
    {k l : Fin (a.len + 1)} (hkl : k ≤ l) :
    (edgewiseStageShellPacket X.1.grid.obj k l hkl).source ≅
      (edgewiseStageShellPacket Y.1.grid.obj k l hkl).source :=
  ((eqToIso (edgewiseStageShellSourceEqVertex X.1.grid.obj k l hkl)).trans
    (vertexIso X Y k)).trans
      (eqToIso (edgewiseStageShellSourceEqVertex Y.1.grid.obj k l hkl)).symm

/-- Raw target-endpoint comparison induced by the selected vertex iso. -/
@[no_expose]
noncomputable def shellTargetIso
    {k l : Fin (a.len + 1)} (hkl : k ≤ l) :
    (edgewiseStageShellPacket X.1.grid.obj k l hkl).target ≅
      (edgewiseStageShellPacket Y.1.grid.obj k l hkl).target :=
  ((eqToIso (edgewiseStageShellTargetEqVertex X.1.grid.obj k l hkl)).trans
    (vertexIso X Y l)).trans
      (eqToIso (edgewiseStageShellTargetEqVertex Y.1.grid.obj k l hkl)).symm

/-- Endpoint-compatible comparison of the literal raw shell spans. -/
@[no_expose]
noncomputable def shellEndpointIso
    {k l : Fin (a.len + 1)} (hkl : k ≤ l) :
    QuillenSpan.EndpointIso
      (edgewiseStageShellPacket X.1.grid.obj k l hkl).span
      (edgewiseStageShellPacket Y.1.grid.obj k l hkl).span
      (shellSourceIso X Y hkl) (shellTargetIso X Y hkl) :=
  by
    simpa only [shellSourceIso, shellTargetIso] using
      ((rawToNormalizedEndpointIso X.1.grid.obj hkl).trans
        (normalizedShellEndpointIso X Y hkl)).trans
          (rawToNormalizedEndpointIso Y.1.grid.obj hkl).symm

set_option backward.isDefEq.respectTransparency false in
/-- The source endpoint comparison is independent of the other shell
endpoint. -/
theorem shellSourceIso_eq
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hkr : k ≤ r) :
    shellSourceIso X Y hkl = shellSourceIso X Y hkr := by
  apply Iso.ext
  simp [shellSourceIso]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The target endpoint comparison is independent of the other shell
endpoint. -/
theorem shellTargetIso_eq
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hrl : r ≤ l) :
    shellTargetIso X Y hkl = shellTargetIso X Y hrl := by
  apply Iso.ext
  simp [shellTargetIso]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The target comparison of the first shell is the source comparison of an
adjacent second shell. -/
theorem shellTargetIso_eq_sourceIso
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r) :
    shellTargetIso X Y hkl = shellSourceIso X Y hlr := by
  apply Iso.ext
  simp [shellSourceIso, shellTargetIso]
  rfl

/-- The second shell comparison with its source endpoint parameter aligned to
the first shell's target parameter. -/
@[no_expose]
noncomputable def shellEndpointIsoRightAligned
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r) :
    QuillenSpan.EndpointIso
      (edgewiseStageShellPacket X.1.grid.obj l r hlr).span
      (edgewiseStageShellPacket Y.1.grid.obj l r hlr).span
      (shellTargetIso X Y hkl) (shellTargetIso X Y hlr) := by
  rw [shellTargetIso_eq_sourceIso X Y hkl hlr]
  exact shellEndpointIso X Y hlr

/-- The long-shell comparison with endpoint parameters aligned to those of
the ordered pair of short shells. -/
@[no_expose]
noncomputable def shellEndpointIsoLongAligned
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r) :
    QuillenSpan.EndpointIso
      (edgewiseStageShellPacket X.1.grid.obj k r (hkl.trans hlr)).span
      (edgewiseStageShellPacket Y.1.grid.obj k r (hkl.trans hlr)).span
      (shellSourceIso X Y hkl) (shellTargetIso X Y hlr) := by
  rw [shellSourceIso_eq X Y hkl (hkl.trans hlr)]
  rw [← shellTargetIso_eq X Y (hkl.trans hlr) hlr]
  exact shellEndpointIso X Y (hkl.trans hlr)

/-- The independently recovered long-shell comparison is the ordered
pullback composite of the short-shell comparisons. -/
theorem shellEndpointIso_comp
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r) :
    edgewiseStageShellEndpointIsoComp X.1.grid.obj Y.1.grid.obj hkl hlr
        (shellEndpointIso X Y hkl)
        (shellEndpointIsoRightAligned X Y hkl hlr) =
      shellEndpointIsoLongAligned X Y hkl hlr :=
  QuillenSpan.EndpointIso.unique _ _

set_option backward.isDefEq.respectTransparency false in
/-- The coherent long-shell apex map restricts to the first short-shell apex
map. -/
theorem shellEndpointIsoLongAligned_hom_left
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r) :
    (shellEndpointIsoLongAligned X Y hkl hlr).1.hom ≫
        edgewiseStageShellToLeft Y.1.grid.obj hkl hlr =
      edgewiseStageShellToLeft X.1.grid.obj hkl hlr ≫
        (shellEndpointIso X Y hkl).1.hom := by
  rw [← shellEndpointIso_comp X Y hkl hlr]
  exact edgewiseStageShellEndpointIsoComp_hom_left
    X.1.grid.obj Y.1.grid.obj hkl hlr
      (shellEndpointIso X Y hkl)
      (shellEndpointIsoRightAligned X Y hkl hlr)

set_option backward.isDefEq.respectTransparency false in
/-- The coherent long-shell apex map restricts to the second short-shell apex
map. -/
theorem shellEndpointIsoLongAligned_hom_right
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r) :
    (shellEndpointIsoLongAligned X Y hkl hlr).1.hom ≫
        edgewiseStageShellToRight Y.1.grid.obj hkl hlr =
      edgewiseStageShellToRight X.1.grid.obj hkl hlr ≫
        (shellEndpointIsoRightAligned X Y hkl hlr).1.hom := by
  rw [← shellEndpointIso_comp X Y hkl hlr]
  exact edgewiseStageShellEndpointIsoComp_hom_right
    X.1.grid.obj Y.1.grid.obj hkl hlr
      (shellEndpointIso X Y hkl)
      (shellEndpointIsoRightAligned X Y hkl hlr)

/-- Tail-shell comparison from `k` to the final simplex vertex. -/
@[no_expose]
noncomputable def tailEndpointIso (k : Fin (a.len + 1)) :=
  shellEndpointIso X Y (Fin.le_last k)

set_option backward.isDefEq.respectTransparency false in
/-- The apex map of a recovered shell comparison is independent of the proof
of its endpoint inequality. -/
theorem shellEndpointIso_apex_hom_proof_irrel
    {k l : Fin (a.len + 1)} (h h' : k ≤ l) :
    (shellEndpointIso X Y h).1.hom = (shellEndpointIso X Y h').1.hom := by
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- Tail-shell apex index equals the corresponding straight-right zero-row
index. -/
theorem tailApexIndexEq (k : Fin (a.len + 1)) :
    (indexFunctor (edgewiseShell a k (Fin.last a.len) (Fin.le_last k))).obj
        (interval (0 : Fin 4) 2 (by decide)) =
      interval 0 (edgewiseRightIndex a k) (Fin.zero_le _) := by
  rw [indexFunctor_obj_interval]
  have hz : edgewiseLeftIndex a (Fin.last a.len) = 0 := by
    apply Fin.ext
    simp only [edgewiseLeftIndex_val, Fin.val_last, Fin.val_zero]
    omega
  exact Arrow.ext hz rfl (Subsingleton.elim _ _)

set_option backward.isDefEq.respectTransparency false in
/-- Tail-shell kernel index equals the corresponding reversed-left zero-row
index. -/
theorem tailKernelIndexEq (k : Fin (a.len + 1)) :
    (indexFunctor (edgewiseShell a k (Fin.last a.len) (Fin.le_last k))).obj
        (interval (0 : Fin 4) 1 (by decide)) =
      interval 0 (edgewiseLeftIndex a k) (Fin.zero_le _) := by
  rw [indexFunctor_obj_interval]
  have hz : edgewiseLeftIndex a (Fin.last a.len) = 0 := by
    apply Fin.ext
    simp only [edgewiseLeftIndex_val, Fin.val_last, Fin.val_zero]
    omega
  exact Arrow.ext hz rfl (Subsingleton.elim _ _)

set_option backward.isDefEq.respectTransparency false in
/-- The source index of a tail shell is its literal cross-vertex interval. -/
theorem tailSourceIndexEq (k : Fin (a.len + 1)) :
    (indexFunctor (edgewiseShell a k (Fin.last a.len) (Fin.le_last k))).obj
        (interval (1 : Fin 4) 2 (by decide)) =
      interval (edgewiseLeftIndex a k) (edgewiseRightIndex a k)
        (edgewiseStageVertex_le a k) := by
  rw [indexFunctor_obj_interval]
  exact Arrow.ext rfl rfl (Subsingleton.elim _ _)

/-- The apex of a tail shell is the corresponding straight-right zero-row
object. -/
theorem tailApex_eq_zeroRowObj
    (A : Stage C (edgewiseQ.obj a).len) (k : Fin (a.len + 1)) :
    (edgewiseStageShellPacket A k (Fin.last a.len) (Fin.le_last k)).span.apex =
      A.zeroRowChain.obj (edgewiseRightIndex a k) :=
  congrArg A.obj.obj (tailApexIndexEq k)

/-- The kernel object of a tail flag is the corresponding reversed-left
zero-row object. -/
theorem tailKernel_eq_zeroRowObj
    (A : Stage C (edgewiseQ.obj a).len) (k : Fin (a.len + 1)) :
    (edgewiseStageShellPacket A k (Fin.last a.len)
        (Fin.le_last k)).flag.kernelObj =
      A.zeroRowChain.obj (edgewiseLeftIndex a k) :=
  congrArg A.obj.obj (tailKernelIndexEq k)

/-- Tail apex comparison transported to the literal zero row. -/
@[no_expose]
noncomputable def tailApexIso (k : Fin (a.len + 1)) :
    X.1.grid.obj.zeroRowChain.obj (edgewiseRightIndex a k) ≅
      Y.1.grid.obj.zeroRowChain.obj (edgewiseRightIndex a k) :=
  (eqToIso (tailApex_eq_zeroRowObj X.1.grid.obj k).symm).trans
    (((tailEndpointIso X Y k).1).trans
      (eqToIso (tailApex_eq_zeroRowObj Y.1.grid.obj k)))

/-- Canonical material flag map for a tail shell. -/
@[no_expose]
noncomputable def tailFlagHom (k : Fin (a.len + 1)) :=
  QuillenSpanFlagHom.endpointCanonical (tailEndpointIso X Y k)
    (edgewiseStageShellPacket X.1.grid.obj k (Fin.last a.len)
      (Fin.le_last k)).flag
    (edgewiseStageShellPacket Y.1.grid.obj k (Fin.last a.len)
      (Fin.le_last k)).flag

/-- Canonical tail-kernel comparison before identifying kernel objects with
zero-row objects. -/
noncomputable def tailKernelMaterialIso (k : Fin (a.len + 1)) :
    (edgewiseStageShellPacket X.1.grid.obj k (Fin.last a.len)
        (Fin.le_last k)).flag.kernelObj ≅
      (edgewiseStageShellPacket Y.1.grid.obj k (Fin.last a.len)
        (Fin.le_last k)).flag.kernelObj := by
  let e := (quillenSpanFlagKernelFunctor
    (edgewiseStageShellPacket Y.1.grid.obj k (Fin.last a.len)
      (Fin.le_last k)).span).mapIso (asIso (tailFlagHom X Y k))
  change (edgewiseStageShellPacket X.1.grid.obj k (Fin.last a.len)
      (Fin.le_last k)).flag.kernelObj ≅
    (edgewiseStageShellPacket Y.1.grid.obj k (Fin.last a.len)
      (Fin.le_last k)).flag.kernelObj at e
  exact e

/-- Tail-kernel comparison transported to the literal zero row. -/
@[no_expose]
noncomputable def tailKernelIso (k : Fin (a.len + 1)) :
    X.1.grid.obj.zeroRowChain.obj (edgewiseLeftIndex a k) ≅
      Y.1.grid.obj.zeroRowChain.obj (edgewiseLeftIndex a k) :=
  (eqToIso (tailKernel_eq_zeroRowObj X.1.grid.obj k).symm).trans
    ((tailKernelMaterialIso X Y k).trans
      (eqToIso (tailKernel_eq_zeroRowObj Y.1.grid.obj k)))

set_option backward.isDefEq.respectTransparency false in
/-- The literal kernel inclusion in a tail flag is the corresponding zero-row
map, after the displayed object equalities. -/
theorem zeroRowMap_eq_tailKernelι
    (A : Stage C (edgewiseQ.obj a).len) (k : Fin (a.len + 1)) :
    A.zeroRowChain.map
        (homOfLE (edgewiseLeftIndex_le_rightIndex a k)) =
      eqToHom (tailKernel_eq_zeroRowObj A k).symm ≫
        (edgewiseStageShellPacket A k (Fin.last a.len)
          (Fin.le_last k)).flag.kernelι ≫
        eqToHom (tailApex_eq_zeroRowObj A k) := by
  let s := edgewiseShell a k (Fin.last a.len) (Fin.le_last k)
  let f := horiz (Fin.zero_le (edgewiseLeftIndex a k))
    (edgewiseLeftIndex_le_rightIndex a k)
  let g := (indexFunctor s).map
    (horiz (show (0 : Fin 4) ≤ 1 by decide)
      (show (1 : Fin 4) ≤ 2 by decide))
  have hIndex : f = eqToHom (tailKernelIndexEq k).symm ≫ g ≫
      eqToHom (tailApexIndexEq k) := by
    apply Arrow.hom_ext <;> exact Subsingleton.elim _ _
  have hMap := congrArg A.obj.map hIndex
  change A.obj.map f = eqToHom (congrArg A.obj.obj (tailKernelIndexEq k)).symm ≫
      A.obj.map g ≫ eqToHom (congrArg A.obj.obj (tailApexIndexEq k))
  simpa only [Functor.map_comp, eqToHom_map] using hMap

@[simp]
theorem tailKernelMaterialIso_hom (k : Fin (a.len + 1)) :
    (tailKernelMaterialIso X Y k).hom = (tailFlagHom X Y k).kernelHom :=
  by
    unfold tailKernelMaterialIso
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Characteristic kernel square of the canonical material tail comparison. -/
@[reassoc]
theorem tailKernelMaterialIso_hom_comp_kernelι
    (k : Fin (a.len + 1)) :
    (tailKernelMaterialIso X Y k).hom ≫
        (edgewiseStageShellPacket Y.1.grid.obj k (Fin.last a.len)
          (Fin.le_last k)).flag.kernelι =
      (edgewiseStageShellPacket X.1.grid.obj k (Fin.last a.len)
          (Fin.le_last k)).flag.kernelι ≫
        (tailEndpointIso X Y k).1.hom := by
  simpa only [tailKernelMaterialIso_hom,
    QuillenSpanFlagData.transport_kernelι,
    QuillenSpanFlagData.endpointTransport_kernelι,
    QuillenSpan.EndpointIso.endpointTransportIso_hom_hom] using
      (tailFlagHom X Y k).kernelHom_kernelι

set_option backward.isDefEq.respectTransparency false in
/-- Kernel and apex tail comparisons commute with the zero-row cross map. -/
@[reassoc]
theorem tailKernelIso_hom_naturality
    (k : Fin (a.len + 1)) :
    X.1.grid.obj.zeroRowChain.map
          (homOfLE (edgewiseLeftIndex_le_rightIndex a k)) ≫
        (tailApexIso X Y k).hom =
      (tailKernelIso X Y k).hom ≫
        Y.1.grid.obj.zeroRowChain.map
          (homOfLE (edgewiseLeftIndex_le_rightIndex a k)) := by
  rw [zeroRowMap_eq_tailKernelι X.1.grid.obj k,
    zeroRowMap_eq_tailKernelι Y.1.grid.obj k]
  simp only [tailApexIso, tailKernelIso, Iso.trans_hom, eqToIso.hom,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  rw [tailKernelMaterialIso_hom_comp_kernelι_assoc X Y k]

/-- Middle naturality with propositionally equal left/right simplex indices. -/
theorem tailKernelApexIso_hom_naturality_of_eq
    {k l : Fin (a.len + 1)} (hkl : k = l)
    (hLR : edgewiseLeftIndex a k ≤ edgewiseRightIndex a l) :
    X.1.grid.obj.zeroRowChain.map (homOfLE hLR) ≫
        (tailApexIso X Y l).hom =
      (tailKernelIso X Y k).hom ≫
        Y.1.grid.obj.zeroRowChain.map (homOfLE hLR) := by
  subst l
  have hproof : hLR = edgewiseLeftIndex_le_rightIndex a k :=
    Subsingleton.elim _ _
  subst hproof
  exact tailKernelIso_hom_naturality X Y k

@[simp]
theorem shellEndpointIsoLongAligned_apex_hom
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r) :
    (shellEndpointIsoLongAligned X Y hkl hlr).1.hom =
      (shellEndpointIso X Y (hkl.trans hlr)).1.hom := by
  unfold shellEndpointIsoLongAligned
  rfl

@[simp]
theorem shellEndpointIsoRightAligned_apex_hom
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r) :
    (shellEndpointIsoRightAligned X Y hkl hlr).1.hom =
      (shellEndpointIso X Y hlr).1.hom := by
  unfold shellEndpointIsoRightAligned
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The long-to-right tail-apex map is the corresponding zero-row map after
the displayed apex object equalities. -/
theorem zeroRowMap_eq_tailApexTransition
    (A : Stage C (edgewiseQ.obj a).len)
    {k l : Fin (a.len + 1)} (hkl : k ≤ l) :
    A.zeroRowChain.map (homOfLE (edgewiseRightIndex_mono hkl)) =
      eqToHom (tailApex_eq_zeroRowObj A k).symm ≫
        edgewiseStageShellToRight A hkl (Fin.le_last l) ≫
        eqToHom (tailApex_eq_zeroRowObj A l) := by
  let f := horiz (Fin.zero_le (edgewiseRightIndex a k))
    (edgewiseRightIndex_mono hkl)
  let g := horiz
    ((edgewiseLeftIndex_anti (Fin.le_last l)).trans
      ((edgewiseLeftIndex_anti hkl).trans
        (edgewiseLeftIndex_le_rightIndex a k)))
    (edgewiseRightIndex_mono hkl)
  have hIndex : f = eqToHom (tailApexIndexEq k).symm ≫ g ≫
      eqToHom (tailApexIndexEq l) := by
    apply Arrow.hom_ext <;> exact Subsingleton.elim _ _
  have hMap := congrArg A.obj.map hIndex
  change A.obj.map f = eqToHom (congrArg A.obj.obj (tailApexIndexEq k)).symm ≫
      A.obj.map g ≫ eqToHom (congrArg A.obj.obj (tailApexIndexEq l))
  simpa only [Functor.map_comp, eqToHom_map] using hMap

set_option backward.isDefEq.respectTransparency false in
/-- The quotient projection to a cross vertex is the normalized tail-shell
left leg after the displayed apex equality. -/
theorem zeroRowCellProjection_eq_normalizedTail_l
    (A : Stage C (edgewiseQ.obj a).len) (k : Fin (a.len + 1)) :
    A.zeroRowCellProjection (edgewiseStageVertex_le a k) =
      eqToHom (tailApex_eq_zeroRowObj A k).symm ≫
        (edgewiseStageShellSpanNormalized A k (Fin.last a.len)
          (Fin.le_last k)).l := by
  let s := edgewiseShell a k (Fin.last a.len) (Fin.le_last k)
  let f := vert (Fin.zero_le (edgewiseLeftIndex a k))
    (edgewiseStageVertex_le a k)
  let g := (indexFunctor s).map
    (vert (show (0 : Fin 4) ≤ 1 by decide)
      (show (1 : Fin 4) ≤ 2 by decide))
  have hIndex : f = eqToHom (tailApexIndexEq k).symm ≫ g ≫
      eqToHom (tailSourceIndexEq k) := by
    apply Arrow.hom_ext <;> exact Subsingleton.elim _ _
  have hMap := congrArg A.obj.map hIndex
  change A.obj.map f =
    eqToHom (congrArg A.obj.obj (tailApexIndexEq k)).symm ≫
      (A.obj.map g ≫
        eqToHom (edgewiseStageShellSourceEqVertex A k
          (Fin.last a.len) (Fin.le_last k)))
  simpa only [Functor.map_comp, eqToHom_map, Category.assoc] using hMap

@[simp]
theorem tailEndpointIso_apex_hom_eq_normalized
    (k : Fin (a.len + 1)) :
    (tailEndpointIso X Y k).1.hom =
      (normalizedShellEndpointIso X Y (Fin.le_last k)).1.hom := by
  unfold tailEndpointIso shellEndpointIso rawToNormalizedEndpointIso
  change (𝟙 _ ≫
      (normalizedShellEndpointIso X Y (Fin.le_last k)).1.hom) ≫ 𝟙 _ = _
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The tail apex comparison induces exactly the selected comparison on the
cross-vertex quotient. -/
theorem tailApexIso_hom_projection (k : Fin (a.len + 1)) :
    (tailApexIso X Y k).hom ≫
        Y.1.grid.obj.zeroRowCellProjection (edgewiseStageVertex_le a k) =
      X.1.grid.obj.zeroRowCellProjection (edgewiseStageVertex_le a k) ≫
        (vertexIso X Y k).hom := by
  rw [zeroRowCellProjection_eq_normalizedTail_l,
    zeroRowCellProjection_eq_normalizedTail_l]
  simp only [tailApexIso, Iso.trans_hom, eqToIso.hom,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  rw [tailEndpointIso_apex_hom_eq_normalized]
  rw [(normalizedShellEndpointIso X Y (Fin.le_last k)).hom_l]

set_option backward.isDefEq.respectTransparency false in
/-- Tail apex comparisons are natural on the straight-right half of the zero
row. -/
@[reassoc]
theorem tailApexIso_hom_naturality
    {k l : Fin (a.len + 1)} (hkl : k ≤ l) :
    X.1.grid.obj.zeroRowChain.map
          (homOfLE (edgewiseRightIndex_mono hkl)) ≫
        (tailApexIso X Y l).hom =
      (tailApexIso X Y k).hom ≫
        Y.1.grid.obj.zeroRowChain.map
          (homOfLE (edgewiseRightIndex_mono hkl)) := by
  rw [zeroRowMap_eq_tailApexTransition X.1.grid.obj hkl,
    zeroRowMap_eq_tailApexTransition Y.1.grid.obj hkl]
  simp only [tailApexIso, Iso.trans_hom, eqToIso.hom,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  have h := shellEndpointIsoLongAligned_hom_right X Y hkl (Fin.le_last l)
  rw [shellEndpointIsoLongAligned_apex_hom,
    shellEndpointIsoRightAligned_apex_hom] at h
  have hk : (shellEndpointIso X Y (hkl.trans (Fin.le_last l))).1.hom =
      (tailEndpointIso X Y k).1.hom := by
    exact shellEndpointIso_apex_hom_proof_irrel X Y _ _
  have hl : (shellEndpointIso X Y (Fin.le_last l)).1.hom =
      (tailEndpointIso X Y l).1.hom := rfl
  rw [hk, hl] at h
  simpa only [Category.assoc] using
    congrArg (fun f ↦
      eqToHom (tailApex_eq_zeroRowObj X.1.grid.obj k).symm ≫
        f ≫ eqToHom (tailApex_eq_zeroRowObj Y.1.grid.obj l)) h.symm

/-- The reversed-left map, cross map, and straight-right map in a tail ladder
compose to the later cross map. -/
theorem zeroRow_tail_ladder
    (A : Stage C (edgewiseQ.obj a).len)
    {k l : Fin (a.len + 1)} (hkl : k ≤ l) :
    A.zeroRowChain.map (homOfLE (edgewiseLeftIndex_anti hkl)) ≫
        A.zeroRowChain.map
          (homOfLE (edgewiseLeftIndex_le_rightIndex a k)) ≫
        A.zeroRowChain.map (homOfLE (edgewiseRightIndex_mono hkl)) =
      A.zeroRowChain.map
        (homOfLE (edgewiseLeftIndex_le_rightIndex a l)) := by
  rw [← A.zeroRowChain.map_comp, ← A.zeroRowChain.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- Tail kernel comparisons are natural on the reversed-left half of the zero
row. -/
theorem tailKernelIso_hom_lower_naturality
    {k l : Fin (a.len + 1)} (hkl : k ≤ l) :
    X.1.grid.obj.zeroRowChain.map
          (homOfLE (edgewiseLeftIndex_anti hkl)) ≫
        (tailKernelIso X Y k).hom =
      (tailKernelIso X Y l).hom ≫
        Y.1.grid.obj.zeroRowChain.map
          (homOfLE (edgewiseLeftIndex_anti hkl)) := by
  let AX := X.1.grid.obj
  let AY := Y.1.grid.obj
  let lX := AX.zeroRowChain.map
    (homOfLE (edgewiseLeftIndex_anti hkl))
  let lY := AY.zeroRowChain.map
    (homOfLE (edgewiseLeftIndex_anti hkl))
  let cXk := AX.zeroRowChain.map
    (homOfLE (edgewiseLeftIndex_le_rightIndex a k))
  let cYk := AY.zeroRowChain.map
    (homOfLE (edgewiseLeftIndex_le_rightIndex a k))
  let cXl := AX.zeroRowChain.map
    (homOfLE (edgewiseLeftIndex_le_rightIndex a l))
  let cYl := AY.zeroRowChain.map
    (homOfLE (edgewiseLeftIndex_le_rightIndex a l))
  let uX := AX.zeroRowChain.map
    (homOfLE (edgewiseRightIndex_mono hkl))
  let uY := AY.zeroRowChain.map
    (homOfLE (edgewiseRightIndex_mono hkl))
  have hcYk : IsAdmissibleMono cYk := by
    change IsAdmissibleMono
      (AY.obj.map (horiz (Fin.zero_le (edgewiseLeftIndex a k))
        (edgewiseLeftIndex_le_rightIndex a k)))
    exact (AY.property.cofiber_triple (Fin.zero_le _)
      (edgewiseLeftIndex_le_rightIndex a k)).1
  have huY : IsAdmissibleMono uY := by
    change IsAdmissibleMono
      (AY.obj.map (horiz (Fin.zero_le (edgewiseRightIndex a k))
        (edgewiseRightIndex_mono hkl)))
    exact (AY.property.cofiber_triple (Fin.zero_le _)
      (edgewiseRightIndex_mono hkl)).1
  let _ : Mono cYk := hcYk.mono
  let _ : Mono uY := huY.mono
  apply (cancel_mono (cYk ≫ uY)).1
  change (lX ≫ (tailKernelIso X Y k).hom) ≫ (cYk ≫ uY) =
    ((tailKernelIso X Y l).hom ≫ lY) ≫ (cYk ≫ uY)
  calc
    (lX ≫ (tailKernelIso X Y k).hom) ≫ (cYk ≫ uY) =
      lX ≫ ((tailKernelIso X Y k).hom ≫ cYk) ≫ uY := by
        simp only [Category.assoc]
    _ = lX ≫ (cXk ≫ (tailApexIso X Y k).hom) ≫ uY := by
      rw [tailKernelIso_hom_naturality]
    _ = lX ≫ cXk ≫ ((tailApexIso X Y k).hom ≫ uY) := by
      simp only [Category.assoc]
    _ = lX ≫ cXk ≫ (uX ≫ (tailApexIso X Y l).hom) := by
      rw [← tailApexIso_hom_naturality X Y hkl]
    _ = (lX ≫ cXk ≫ uX) ≫ (tailApexIso X Y l).hom := by
      simp only [Category.assoc]
    _ = cXl ≫ (tailApexIso X Y l).hom := by
      rw [zeroRow_tail_ladder AX hkl]
    _ = (tailKernelIso X Y l).hom ≫ cYl :=
      tailKernelIso_hom_naturality X Y l
    _ = (tailKernelIso X Y l).hom ≫ (lY ≫ cYk ≫ uY) := by
      rw [zeroRow_tail_ladder AY hkl]
    _ = ((tailKernelIso X Y l).hom ≫ lY) ≫ (cYk ≫ uY) := by
      simp only [Category.assoc]

/-- Simplex vertex indexing a position in the reversed-left half of the
edgewise zero row. -/
@[no_expose]
def lowerVertexOfZeroRowIndex
    (j : Fin ((edgewiseQ.obj a).len + 1)) (hj : j.val ≤ a.len) :
    Fin (a.len + 1) :=
  ⟨a.len - j.val, by omega⟩

/-- Simplex vertex indexing a position in the straight-right half of the
edgewise zero row. -/
@[no_expose]
def upperVertexOfZeroRowIndex
    (j : Fin ((edgewiseQ.obj a).len + 1)) (hj : ¬ j.val ≤ a.len) :
    Fin (a.len + 1) :=
  ⟨j.val - (a.len + 1), by
    have hjlt : j.val < 2 * a.len + 2 := by
      simpa only [edgewiseQ_obj_len] using j.isLt
    have hgt : a.len < j.val := Nat.lt_of_not_ge hj
    omega⟩

@[simp]
theorem edgewiseLeftIndex_lowerVertexOfZeroRowIndex
    (j : Fin ((edgewiseQ.obj a).len + 1)) (hj : j.val ≤ a.len) :
    edgewiseLeftIndex a (lowerVertexOfZeroRowIndex j hj) = j := by
  apply Fin.ext
  simp only [edgewiseLeftIndex_val, lowerVertexOfZeroRowIndex]
  omega

@[simp]
theorem edgewiseRightIndex_upperVertexOfZeroRowIndex
    (j : Fin ((edgewiseQ.obj a).len + 1)) (hj : ¬ j.val ≤ a.len) :
    edgewiseRightIndex a (upperVertexOfZeroRowIndex j hj) = j := by
  apply Fin.ext
  simp only [edgewiseRightIndex_val, upperVertexOfZeroRowIndex]
  omega

/-- Transport a component isomorphism along a displayed equality of finite
chain indices. -/
@[no_expose]
def transportComponentIso
    {m : ℕ} (F G : ComposableArrows C m)
    {p i : Fin (m + 1)} (h : p = i) (e : F.obj p ≅ G.obj p) :
    F.obj i ≅ G.obj i :=
  (eqToIso (congrArg F.obj h).symm).trans
    (e.trans (eqToIso (congrArg G.obj h)))

omit [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
    [ExactCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- Naturality is preserved when both endpoint components are transported
along displayed index equalities. -/
theorem transportComponentIso_naturality
    {m : ℕ} (F G : ComposableArrows C m)
    {p q i j : Fin (m + 1)}
    (hpq : p ≤ q) (hij : i ≤ j)
    (hi : p = i) (hj : q = j)
    (ep : F.obj p ≅ G.obj p) (eq : F.obj q ≅ G.obj q)
    (h : F.map (homOfLE hpq) ≫ eq.hom =
      ep.hom ≫ G.map (homOfLE hpq)) :
    F.map (homOfLE hij) ≫ (transportComponentIso F G hj eq).hom =
      (transportComponentIso F G hi ep).hom ≫
        G.map (homOfLE hij) := by
  subst i
  subst j
  simpa only [transportComponentIso, Iso.trans_hom, eqToIso.hom,
    eqToHom_refl, Category.id_comp, Category.comp_id] using h

/-- Pointwise zero-row comparison, split into the reversed-left kernel half
and the straight-right apex half. -/
@[no_expose]
noncomputable def zeroRowComponentIso
    (j : Fin ((edgewiseQ.obj a).len + 1)) :
    X.1.grid.obj.zeroRowChain.obj j ≅ Y.1.grid.obj.zeroRowChain.obj j := by
  by_cases hj : j.val ≤ a.len
  · let k := lowerVertexOfZeroRowIndex j hj
    let h := edgewiseLeftIndex_lowerVertexOfZeroRowIndex j hj
    exact transportComponentIso X.1.grid.obj.zeroRowChain
      Y.1.grid.obj.zeroRowChain h (tailKernelIso X Y k)
  · let k := upperVertexOfZeroRowIndex j hj
    let h := edgewiseRightIndex_upperVertexOfZeroRowIndex j hj
    exact transportComponentIso X.1.grid.obj.zeroRowChain
      Y.1.grid.obj.zeroRowChain h (tailApexIso X Y k)

theorem zeroRowComponentIso_of_le
    (j : Fin ((edgewiseQ.obj a).len + 1)) (hj : j.val ≤ a.len) :
    zeroRowComponentIso X Y j =
      transportComponentIso X.1.grid.obj.zeroRowChain
        Y.1.grid.obj.zeroRowChain
        (edgewiseLeftIndex_lowerVertexOfZeroRowIndex j hj)
        (tailKernelIso X Y (lowerVertexOfZeroRowIndex j hj)) := by
  unfold zeroRowComponentIso
  rw [dite_eq_left hj]

theorem zeroRowComponentIso_of_not_le
    (j : Fin ((edgewiseQ.obj a).len + 1)) (hj : ¬ j.val ≤ a.len) :
    zeroRowComponentIso X Y j =
      transportComponentIso X.1.grid.obj.zeroRowChain
        Y.1.grid.obj.zeroRowChain
        (edgewiseRightIndex_upperVertexOfZeroRowIndex j hj)
        (tailApexIso X Y (upperVertexOfZeroRowIndex j hj)) := by
  unfold zeroRowComponentIso
  rw [dite_eq_right hj]

set_option backward.isDefEq.respectTransparency false in
/-- The pointwise zero-row comparisons commute with every successor map. -/
theorem zeroRowComponentIso_succ_naturality
    (i : ℕ) (hi : i < (edgewiseQ.obj a).len) :
    X.1.grid.obj.zeroRowChain.map' i (i + 1) (Nat.le_succ i)
          (Nat.succ_le_iff.mpr hi) ≫
        (zeroRowComponentIso X Y ⟨i + 1, by omega⟩).hom =
      (zeroRowComponentIso X Y ⟨i, by omega⟩).hom ≫
        Y.1.grid.obj.zeroRowChain.map' i (i + 1) (Nat.le_succ i)
          (Nat.succ_le_iff.mpr hi) := by
  let j₀ : Fin ((edgewiseQ.obj a).len + 1) := ⟨i, by omega⟩
  let j₁ : Fin ((edgewiseQ.obj a).len + 1) := ⟨i + 1, by omega⟩
  have hj₀j₁ : j₀ ≤ j₁ := by
    rw [Fin.le_iff_val_le_val]
    exact Nat.le_succ i
  change X.1.grid.obj.zeroRowChain.map (homOfLE hj₀j₁) ≫
        (zeroRowComponentIso X Y j₁).hom =
      (zeroRowComponentIso X Y j₀).hom ≫
        Y.1.grid.obj.zeroRowChain.map (homOfLE hj₀j₁)
  by_cases hLower : i < a.len
  · have hj₀ : j₀.val ≤ a.len := by dsimp only [j₀]; omega
    have hj₁ : j₁.val ≤ a.len := by dsimp only [j₁]; omega
    rw [zeroRowComponentIso_of_le X Y j₀ hj₀,
      zeroRowComponentIso_of_le X Y j₁ hj₁]
    let l := lowerVertexOfZeroRowIndex j₀ hj₀
    let k := lowerVertexOfZeroRowIndex j₁ hj₁
    have hkl : k ≤ l := by
      rw [Fin.le_iff_val_le_val]
      dsimp only [k, l, lowerVertexOfZeroRowIndex, j₀, j₁]
      omega
    exact transportComponentIso_naturality
      X.1.grid.obj.zeroRowChain Y.1.grid.obj.zeroRowChain
      (edgewiseLeftIndex_anti hkl) hj₀j₁
      (edgewiseLeftIndex_lowerVertexOfZeroRowIndex j₀ hj₀)
      (edgewiseLeftIndex_lowerVertexOfZeroRowIndex j₁ hj₁)
      (tailKernelIso X Y l) (tailKernelIso X Y k)
      (tailKernelIso_hom_lower_naturality X Y hkl)
  · by_cases hMiddle : i = a.len
    · subst i
      have hj₀ : j₀.val ≤ a.len := by dsimp only [j₀]; omega
      have hj₁ : ¬ j₁.val ≤ a.len := by dsimp only [j₁]; omega
      rw [zeroRowComponentIso_of_le X Y j₀ hj₀,
        zeroRowComponentIso_of_not_le X Y j₁ hj₁]
      let kL := lowerVertexOfZeroRowIndex j₀ hj₀
      let kU := upperVertexOfZeroRowIndex j₁ hj₁
      have hkLU : kL = kU := by
        apply Fin.ext
        dsimp only [kL, kU, lowerVertexOfZeroRowIndex,
          upperVertexOfZeroRowIndex, j₀, j₁]
        omega
      let hLR : edgewiseLeftIndex a kL ≤ edgewiseRightIndex a kU := by
        rw [hkLU]
        exact edgewiseLeftIndex_le_rightIndex a kU
      exact transportComponentIso_naturality
        X.1.grid.obj.zeroRowChain Y.1.grid.obj.zeroRowChain
        hLR hj₀j₁
        (edgewiseLeftIndex_lowerVertexOfZeroRowIndex j₀ hj₀)
        (edgewiseRightIndex_upperVertexOfZeroRowIndex j₁ hj₁)
        (tailKernelIso X Y kL) (tailApexIso X Y kU)
        (tailKernelApexIso_hom_naturality_of_eq X Y hkLU hLR)
    · have hUpper : a.len < i := by omega
      have hj₀ : ¬ j₀.val ≤ a.len := by dsimp only [j₀]; omega
      have hj₁ : ¬ j₁.val ≤ a.len := by dsimp only [j₁]; omega
      rw [zeroRowComponentIso_of_not_le X Y j₀ hj₀,
        zeroRowComponentIso_of_not_le X Y j₁ hj₁]
      let k := upperVertexOfZeroRowIndex j₀ hj₀
      let l := upperVertexOfZeroRowIndex j₁ hj₁
      have hkl : k ≤ l := by
        rw [Fin.le_iff_val_le_val]
        dsimp only [k, l, upperVertexOfZeroRowIndex, j₀, j₁]
        omega
      exact transportComponentIso_naturality
        X.1.grid.obj.zeroRowChain Y.1.grid.obj.zeroRowChain
        (edgewiseRightIndex_mono hkl) hj₀j₁
        (edgewiseRightIndex_upperVertexOfZeroRowIndex j₀ hj₀)
        (edgewiseRightIndex_upperVertexOfZeroRowIndex j₁ hj₁)
        (tailApexIso X Y k) (tailApexIso X Y l)
        (tailApexIso_hom_naturality X Y hkl)

/-- Natural isomorphism between the two material zero-row chains. -/
@[no_expose]
noncomputable def zeroRowIso :
    X.1.grid.obj.zeroRowChain ≅ Y.1.grid.obj.zeroRowChain :=
  ComposableArrows.isoMk (zeroRowComponentIso X Y)
    (zeroRowComponentIso_succ_naturality X Y)

set_option backward.isDefEq.respectTransparency false in
/-- On a straight-right index, the assembled component is the tail apex
comparison. -/
theorem zeroRowComponentIso_right (k : Fin (a.len + 1)) :
    zeroRowComponentIso X Y (edgewiseRightIndex a k) =
      tailApexIso X Y k := by
  have hj : ¬ (edgewiseRightIndex a k).val ≤ a.len := by
    simp only [edgewiseRightIndex_val]
    omega
  rw [zeroRowComponentIso_of_not_le X Y _ hj]
  apply Iso.ext
  unfold transportComponentIso
  simp only [Iso.trans_hom, eqToIso.hom]
  let hR := edgewiseRightIndex_upperVertexOfZeroRowIndex
    (edgewiseRightIndex a k) hj
  have hk : upperVertexOfZeroRowIndex (edgewiseRightIndex a k) hj = k := by
    apply Fin.ext
    simp only [upperVertexOfZeroRowIndex, edgewiseRightIndex_val]
    omega
  symm
  apply (conj_eqToHom_iff_heq _ _
    (congrArg X.1.grid.obj.zeroRowChain.obj hR).symm
    (congrArg Y.1.grid.obj.zeroRowChain.obj hR).symm).2
  exact congr_arg_heq (fun z ↦ (tailApexIso X Y z).hom) hk.symm

@[simp]
theorem zeroRowIso_hom_app_right (k : Fin (a.len + 1)) :
    (zeroRowIso X Y).hom.app (edgewiseRightIndex a k) =
      (tailApexIso X Y k).hom := by
  change (zeroRowComponentIso X Y (edgewiseRightIndex a k)).hom = _
  rw [zeroRowComponentIso_right X Y k]

/-- Stage isomorphism reconstructed from the coherent material zero row. -/
@[no_expose]
noncomputable def stageIso : X.1.grid.obj ≅ Y.1.grid.obj :=
  X.1.grid.obj.isoOfZeroRowIso (zeroRowIso X Y)

set_option backward.isDefEq.respectTransparency false in
/-- The reconstructed Stage comparison has exactly the selected
exact-category isomorphism on every cross vertex. -/
theorem stageIso_hom_app_cross (k : Fin (a.len + 1)) :
    (stageIso X Y).hom.hom.app
        (interval (edgewiseLeftIndex a k) (edgewiseRightIndex a k)
          (edgewiseStageVertex_le a k)) =
      (vertexIso X Y k).hom := by
  rw [stageIso, Stage.isoOfZeroRowIso_hom_app_interval]
  let p := X.1.grid.obj.zeroRowCellProjection (edgewiseStageVertex_le a k)
  let _ : Epi p :=
    (X.1.grid.obj.zeroRowCellProjection_admissibleEpi
      (edgewiseStageVertex_le a k)).epi
  apply (cancel_epi p).1
  change p ≫ X.1.grid.obj.cellHomOfZeroRowHom
      (zeroRowIso X Y).hom (edgewiseStageVertex_le a k) =
    p ≫ (vertexIso X Y k).hom
  rw [Stage.zeroRowCellProjection_cellHomOfZeroRowHom]
  rw [zeroRowIso_hom_app_right]
  exact tailApexIso_hom_projection X Y k

/-- The reconstructed Stage isomorphism as an isomorphism in the pointwise
weak-equivalence category. -/
@[no_expose]
noncomputable def gridIso : X.1.grid ≅ Y.1.grid :=
  WideSubcategory.isoMk (stageIso X Y)
    ((stageWeak C (edgewiseQ.obj a).len).of_isIso (stageIso X Y).hom)
    ((stageWeak C (edgewiseQ.obj a).len).of_isIso (stageIso X Y).inv)

/-- The weak-Stage comparison has the selected exact-category isomorphism at
every extracted cross vertex. -/
theorem gridIso_vertexIso (k : Fin (a.len + 1)) :
    edgewiseStageVertexIso (gridIso X Y).hom k = vertexIso X Y k := by
  apply Iso.ext
  rw [edgewiseStageVertexIso_hom]
  exact stageIso_hom_app_cross X Y k

/-- The reconstructed weak-Stage comparison induces exactly the original
comparison of extracted Quillen simplices. -/
theorem gridIso_map :
    (edgewiseStageQuillenSimplexFunctor C a).map (gridIso X Y).hom =
      (extractedIso X Y).hom := by
  apply NatTrans.ext
  funext k
  rw [edgewiseStageQuillenSimplexFunctor_map,
    edgewiseStageQuillenSimplexMap_app, gridIso_vertexIso]
  exact congrArg Iso.hom (vertexIso_underlyingIso X Y k)

/-- A direct morphism between arbitrary objects of one strict Stage-grid
fiber. -/
@[no_expose]
noncomputable def fiberHom : X ⟶ Y := by
  let g := (gridIso X Y).hom
  let dIso := retainedDiscreteIso X Y
  let qIso := retainedIso X Y
  let eNat := extractedIso X Y
  have hMap :
      (edgewiseStageQuillenSimplexFunctor C a).map g = eNat.hom :=
    gridIso_map X Y
  have hW :
      (edgewiseStageQuillenSimplexFunctor C a).map g ≫ Y.1.obj.hom =
        X.1.obj.hom ≫
          (quillenQSimplexDiscreteInclusion C a).map dIso.hom := by
    rw [hMap]
    have hIsoComp :
        eNat.hom ≫ Y.1.agreementIso.hom =
          X.1.agreementIso.hom ≫ qIso.hom := by
      change (X.1.agreementIso.hom ≫ qIso.hom ≫
          Y.1.agreementIso.inv) ≫ Y.1.agreementIso.hom =
        X.1.agreementIso.hom ≫ qIso.hom
      calc
        (X.1.agreementIso.hom ≫ qIso.hom ≫
            Y.1.agreementIso.inv) ≫ Y.1.agreementIso.hom =
          X.1.agreementIso.hom ≫
            ((qIso.hom ≫ Y.1.agreementIso.inv) ≫
              Y.1.agreementIso.hom) := Category.assoc _ _ _
        _ = X.1.agreementIso.hom ≫
            (qIso.hom ≫
              (Y.1.agreementIso.inv ≫ Y.1.agreementIso.hom)) :=
          congrArg (fun f ↦ X.1.agreementIso.hom ≫ f)
            (Category.assoc _ _ _)
        _ = X.1.agreementIso.hom ≫ (qIso.hom ≫ 𝟙 _) :=
          congrArg (fun f ↦
            X.1.agreementIso.hom ≫ (qIso.hom ≫ f))
            Y.1.agreementIso.inv_hom_id
        _ = X.1.agreementIso.hom ≫ qIso.hom := by
          rw [Category.comp_id]
    have hIsoComp' := hIsoComp
    simp only [QuillenStageGridLift.agreementIso_hom] at hIsoComp'
    change eNat.hom ≫ Y.1.obj.hom =
      X.1.obj.hom ≫ qIso.hom at hIsoComp'
    apply eq_of_heq
    exact heq_of_eq hIsoComp'
  let fComma : X.1.obj ⟶ Y.1.obj :=
    { left := g
      right := dIso.hom
      w := hW }
  let fLift : X.1 ⟶ Y.1 := ObjectProperty.homMk fComma
  refine ⟨fLift, ?_⟩
  apply IsHomLift.of_fac
    (quillenStageGridQProjection C a)
    (𝟙 (Discrete.mk q)) fLift X.2 Y.2
  exact Subsingleton.elim _ _

end QuillenStageGridFiberComparison

set_option linter.style.haveILetI false in
/-- Every strict fiber of the retained Quillen Stage-grid projection is
categorically connected. -/
theorem quillenStageGridFiber_isConnected
    {a : SimplexCategory} (q : QuillenQSimplex C a) :
    IsConnected (QuillenStageGridFiber q) := by
  letI : Nonempty (QuillenStageGridFiber q) :=
    quillenStageGridFiber_nonempty q
  apply zigzag_isConnected
  intro X Y
  exact Relation.ReflTransGen.single
    (Zag.of_hom (QuillenStageGridFiberComparison.fiberHom X Y))

/-- The retained-Q projection is final in every simplex degree. -/
theorem quillenStageGridQProjection_final
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    (a : SimplexCategory) :
    (quillenStageGridQProjection C a).Final := by
  apply (quillenStageGridQProjection_final_iff C a).mpr
  exact fun q ↦ quillenStageGridFiber_isConnected q

/-- The retained-Q projection is initial in every simplex degree. -/
theorem quillenStageGridQProjection_initial
    (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    (a : SimplexCategory) :
    (quillenStageGridQProjection C a).Initial := by
  apply (quillenStageGridQProjection_initial_iff C a).mpr
  exact fun q ↦ quillenStageGridFiber_isConnected q

end AlgebraicKTheory

end
