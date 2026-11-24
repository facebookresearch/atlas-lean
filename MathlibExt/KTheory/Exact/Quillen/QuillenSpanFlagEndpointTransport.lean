/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.KTheory.Exact.Quillen.QuillenSpanEndpointNaturality
public import MathlibExt.KTheory.Exact.Quillen.SpanFlagGrothendieck

/-!
# Endpoint transport for flagged Quillen spans

Isomorphisms of the source and target endpoints transport a raw admissible
Quillen span by postcomposing its two legs.  An explicit six-cell flag over the
span transports with it: the kernel, pushout, and quotient objects are retained,
while the endpoint maps are conjugated by the inverse endpoint isomorphisms.

The four admissible exact sequences and the pushout square are transported
along object isomorphisms.  Reflexive, successive, and inverse endpoint
transport laws are stated after the explicit fixed-endpoint span isomorphisms
needed to identify their indexed flag types.  A C1B endpoint-compatible apex
isomorphism then gives an ordinary span isomorphism and the canonical material
flag comparison used by later composition coherence.

This file constructs no span-composition coherence, Stage reconstruction,
fiber connectedness, contractibility, weak equivalence, or Q/S comparison.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

namespace QuillenSpan

/-- Transport both endpoints of a raw Quillen span along isomorphisms,
retaining its apex and postcomposing its two legs. -/
noncomputable def endpointTransport {X X' Y Y' : C}
    (S : QuillenSpan X Y) (eX : X ≅ X') (eY : Y ≅ Y') :
    QuillenSpan X' Y' where
  apex := S.apex
  l := S.l ≫ eX.hom
  r := S.r ≫ eY.hom
  wl := admissibleEpi_comp.comp_mem _ _ S.wl
    (IsAdmissibleEpi.of_isIso eX.hom)
  wr := admissibleMono_comp.comp_mem _ _ S.wr
    (IsAdmissibleMono.of_isIso eY.hom)

@[simp]
theorem endpointTransport_apex {X X' Y Y' : C}
    (S : QuillenSpan X Y) (eX : X ≅ X') (eY : Y ≅ Y') :
    (endpointTransport S eX eY).apex = S.apex :=
  rfl

@[simp]
theorem endpointTransport_l {X X' Y Y' : C}
    (S : QuillenSpan X Y) (eX : X ≅ X') (eY : Y ≅ Y') :
    (endpointTransport S eX eY).l = S.l ≫ eX.hom :=
  rfl

@[simp]
theorem endpointTransport_r {X X' Y Y' : C}
    (S : QuillenSpan X Y) (eX : X ≅ X') (eY : Y ≅ Y') :
    (endpointTransport S eX eY).r = S.r ≫ eY.hom :=
  rfl

/-- The transported left leg remains an admissible epimorphism. -/
theorem endpointTransport_wl {X X' Y Y' : C}
    (S : QuillenSpan X Y) (eX : X ≅ X') (eY : Y ≅ Y') :
    IsAdmissibleEpi (endpointTransport S eX eY).l :=
  (endpointTransport S eX eY).wl

/-- The transported right leg remains an admissible monomorphism. -/
theorem endpointTransport_wr {X X' Y Y' : C}
    (S : QuillenSpan X Y) (eX : X ≅ X') (eY : Y ≅ Y') :
    IsAdmissibleMono (endpointTransport S eX eY).r :=
  (endpointTransport S eX eY).wr

/-- Reflexive endpoint transport is isomorphic to the original raw span. -/
noncomputable def endpointTransportReflIso {X Y : C}
    (S : QuillenSpan X Y) :
    endpointTransport S (Iso.refl X) (Iso.refl Y) ≅ S :=
  Span.mkIso (Iso.refl S.apex)
    (by simp [endpointTransport])
    (by simp [endpointTransport])

/-- Direct endpoint transport along composites is isomorphic to successive
endpoint transport. -/
noncomputable def endpointTransportTransIso
    {X X' X'' Y Y' Y'' : C} (S : QuillenSpan X Y)
    (eX : X ≅ X') (eY : Y ≅ Y')
    (fX : X' ≅ X'') (fY : Y' ≅ Y'') :
    endpointTransport S (eX.trans fX) (eY.trans fY) ≅
      endpointTransport (endpointTransport S eX eY) fX fY :=
  Span.mkIso (Iso.refl S.apex)
    (by simp [endpointTransport, Category.assoc])
    (by simp [endpointTransport, Category.assoc])

/-- Endpoint transport followed by transport along the inverse endpoint
isomorphisms is isomorphic to the original raw span. -/
noncomputable def endpointTransportSymmIso
    {X X' Y Y' : C} (S : QuillenSpan X Y)
    (eX : X ≅ X') (eY : Y ≅ Y') :
    endpointTransport (endpointTransport S eX eY) eX.symm eY.symm ≅ S :=
  Span.mkIso (Iso.refl S.apex)
    (by simp [endpointTransport, Category.assoc])
    (by simp [endpointTransport, Category.assoc])

@[simp]
theorem endpointTransportReflIso_apex {X Y : C}
    (S : QuillenSpan X Y) :
    Span.SpanBicat.apexIso (endpointTransportReflIso S) = Iso.refl S.apex :=
  rfl

@[simp]
theorem endpointTransportTransIso_apex
    {X X' X'' Y Y' Y'' : C} (S : QuillenSpan X Y)
    (eX : X ≅ X') (eY : Y ≅ Y')
    (fX : X' ≅ X'') (fY : Y' ≅ Y'') :
    Span.SpanBicat.apexIso (endpointTransportTransIso S eX eY fX fY) =
      Iso.refl S.apex :=
  rfl

@[simp]
theorem endpointTransportSymmIso_apex
    {X X' Y Y' : C} (S : QuillenSpan X Y)
    (eX : X ≅ X') (eY : Y ≅ Y') :
    Span.SpanBicat.apexIso (endpointTransportSymmIso S eX eY) =
      Iso.refl S.apex :=
  rfl

end QuillenSpan

/-- Transport explicit flag data together with both endpoints of its raw
span.  Material kernel, pushout, and quotient objects are retained. -/
noncomputable def QuillenSpanFlagData.endpointTransport
    {X X' Y Y' : C} {S : QuillenSpan X Y}
    (eX : X ≅ X') (eY : Y ≅ Y') (A : QuillenSpanFlagData S) :
    QuillenSpanFlagData (QuillenSpan.endpointTransport S eX eY) := by
  let S' := QuillenSpan.endpointTransport S eX eY
  let q' : Y' ⟶ A.quotientObj := eY.inv ≫ A.quotientπ
  let x' : X' ⟶ A.pushoutObj := eX.inv ≫ A.sourceToPushout
  let y' : Y' ⟶ A.pushoutObj := eY.inv ≫ A.targetToPushout
  have wKernel : A.kernelι ≫ S'.l = 0 := by
    rw [show S'.l = S.l ≫ eX.hom from rfl, ← Category.assoc,
      A.kernel_left_zero, zero_comp]
  have wRight : S'.r ≫ q' = 0 := by
    change (S.r ≫ eY.hom) ≫ (eY.inv ≫ A.quotientπ) = 0
    rw [Category.assoc, eY.hom_inv_id_assoc]
    exact A.right_quotient_zero
  have sq' : IsPushout S'.l S'.r x' y' := by
    apply A.pushoutSquare.of_iso (Iso.refl S.apex) eX eY
      (Iso.refl A.pushoutObj)
    · simp [S', QuillenSpan.endpointTransport]
    · simp [S', QuillenSpan.endpointTransport]
    · simp [x']
    · simp [y']
  have wTargetPQ : y' ≫ A.pushoutToQuotient = q' := by
    calc
      y' ≫ A.pushoutToQuotient =
          eY.inv ≫ (A.targetToPushout ≫ A.pushoutToQuotient) :=
        Category.assoc _ _ _
      _ = eY.inv ≫ A.quotientπ :=
        congrArg (fun f => eY.inv ≫ f) A.target_pushoutToQuotient
      _ = q' := rfl
  have wSourcePQ : x' ≫ A.pushoutToQuotient = 0 := by
    calc
      x' ≫ A.pushoutToQuotient =
          eX.inv ≫ (A.sourceToPushout ≫ A.pushoutToQuotient) :=
        Category.assoc _ _ _
      _ = eX.inv ≫ 0 :=
        congrArg (fun f => eX.inv ≫ f) A.source_pushoutToQuotient_zero
      _ = 0 := by simp
  have wKernelTarget : (A.kernelι ≫ S'.r) ≫ y' = 0 := by
    calc
      (A.kernelι ≫ S'.r) ≫ y' =
          (A.kernelι ≫ S.r) ≫ A.targetToPushout := by
        simp [S', y', QuillenSpan.endpointTransport, Category.assoc]
      _ = 0 := A.kernel_targetToPushout_zero
  let leftOld : ShortComplex C :=
    ShortComplex.mk A.kernelι S.l A.kernel_left_zero
  let leftNew : ShortComplex C :=
    ShortComplex.mk A.kernelι S'.l wKernel
  have leftIso : leftOld ≅ leftNew :=
    ShortComplex.isoMk (Iso.refl A.kernelObj) (Iso.refl S.apex) eX
      (by simp [leftOld, leftNew])
      (by simp [leftOld, leftNew, S', QuillenSpan.endpointTransport])
  have hLeft : IsAdmissibleExact leftNew :=
    isAdmissibleExact_of_iso leftIso A.kernel_apex_source_exact
  let rightOld : ShortComplex C :=
    ShortComplex.mk S.r A.quotientπ A.right_quotient_zero
  let rightNew : ShortComplex C :=
    ShortComplex.mk S'.r q' wRight
  have rightIso : rightOld ≅ rightNew :=
    ShortComplex.isoMk (Iso.refl S.apex) eY (Iso.refl A.quotientObj)
      (by simp [rightOld, rightNew, S', QuillenSpan.endpointTransport])
      (by simp [rightOld, rightNew, q'])
  have hRight : IsAdmissibleExact rightNew :=
    isAdmissibleExact_of_iso rightIso A.apex_target_quotient_exact
  let lowerLeftOld : ShortComplex C :=
    ShortComplex.mk (A.kernelι ≫ S.r) A.targetToPushout
      A.kernel_targetToPushout_zero
  let lowerLeftNew : ShortComplex C :=
    ShortComplex.mk (A.kernelι ≫ S'.r) y' wKernelTarget
  have lowerLeftIso : lowerLeftOld ≅ lowerLeftNew :=
    ShortComplex.isoMk (Iso.refl A.kernelObj) eY (Iso.refl A.pushoutObj)
      (by
        simp [lowerLeftOld, lowerLeftNew, S',
          QuillenSpan.endpointTransport, Category.assoc])
      (by simp [lowerLeftOld, lowerLeftNew, y'])
  have hLowerLeft : IsAdmissibleExact lowerLeftNew :=
    isAdmissibleExact_of_iso lowerLeftIso A.kernel_target_pushout_exact
  let lowerRightOld : ShortComplex C :=
    ShortComplex.mk A.sourceToPushout A.pushoutToQuotient
      A.source_pushoutToQuotient_zero
  let lowerRightNew : ShortComplex C :=
    ShortComplex.mk x' A.pushoutToQuotient wSourcePQ
  have lowerRightIso : lowerRightOld ≅ lowerRightNew :=
    ShortComplex.isoMk eX (Iso.refl A.pushoutObj)
      (Iso.refl A.quotientObj)
      (by simp [lowerRightOld, lowerRightNew, x'])
      (by simp [lowerRightOld, lowerRightNew])
  have hLowerRight : IsAdmissibleExact lowerRightNew :=
    isAdmissibleExact_of_iso lowerRightIso A.source_pushout_quotient_exact
  exact
    { kernelObj := A.kernelObj
      pushoutObj := A.pushoutObj
      quotientObj := A.quotientObj
      kernelι := A.kernelι
      quotientπ := q'
      sourceToPushout := x'
      targetToPushout := y'
      pushoutToQuotient := A.pushoutToQuotient
      kernel_left_zero := wKernel
      right_quotient_zero := wRight
      pushoutSquare := sq'
      target_pushoutToQuotient := wTargetPQ
      source_pushoutToQuotient_zero := wSourcePQ
      kernel_targetToPushout_zero := wKernelTarget
      kernel_apex_source_exact := hLeft
      apex_target_quotient_exact := hRight
      kernel_target_pushout_exact := hLowerLeft
      source_pushout_quotient_exact := hLowerRight }

@[simp]
theorem QuillenSpanFlagData.endpointTransport_kernelObj
    {X X' Y Y' : C} {S : QuillenSpan X Y}
    (eX : X ≅ X') (eY : Y ≅ Y') (A : QuillenSpanFlagData S) :
    (A.endpointTransport eX eY).kernelObj = A.kernelObj :=
  rfl

@[simp]
theorem QuillenSpanFlagData.endpointTransport_pushoutObj
    {X X' Y Y' : C} {S : QuillenSpan X Y}
    (eX : X ≅ X') (eY : Y ≅ Y') (A : QuillenSpanFlagData S) :
    (A.endpointTransport eX eY).pushoutObj = A.pushoutObj :=
  rfl

@[simp]
theorem QuillenSpanFlagData.endpointTransport_quotientObj
    {X X' Y Y' : C} {S : QuillenSpan X Y}
    (eX : X ≅ X') (eY : Y ≅ Y') (A : QuillenSpanFlagData S) :
    (A.endpointTransport eX eY).quotientObj = A.quotientObj :=
  rfl

@[simp]
theorem QuillenSpanFlagData.endpointTransport_kernelι
    {X X' Y Y' : C} {S : QuillenSpan X Y}
    (eX : X ≅ X') (eY : Y ≅ Y') (A : QuillenSpanFlagData S) :
    (A.endpointTransport eX eY).kernelι = A.kernelι :=
  rfl

@[simp]
theorem QuillenSpanFlagData.endpointTransport_quotientπ
    {X X' Y Y' : C} {S : QuillenSpan X Y}
    (eX : X ≅ X') (eY : Y ≅ Y') (A : QuillenSpanFlagData S) :
    (A.endpointTransport eX eY).quotientπ = eY.inv ≫ A.quotientπ :=
  rfl

@[simp]
theorem QuillenSpanFlagData.endpointTransport_sourceToPushout
    {X X' Y Y' : C} {S : QuillenSpan X Y}
    (eX : X ≅ X') (eY : Y ≅ Y') (A : QuillenSpanFlagData S) :
    (A.endpointTransport eX eY).sourceToPushout =
      eX.inv ≫ A.sourceToPushout :=
  rfl

@[simp]
theorem QuillenSpanFlagData.endpointTransport_targetToPushout
    {X X' Y Y' : C} {S : QuillenSpan X Y}
    (eX : X ≅ X') (eY : Y ≅ Y') (A : QuillenSpanFlagData S) :
    (A.endpointTransport eX eY).targetToPushout =
      eY.inv ≫ A.targetToPushout :=
  rfl

@[simp]
theorem QuillenSpanFlagData.endpointTransport_pushoutToQuotient
    {X X' Y Y' : C} {S : QuillenSpan X Y}
    (eX : X ≅ X') (eY : Y ≅ Y') (A : QuillenSpanFlagData S) :
    (A.endpointTransport eX eY).pushoutToQuotient =
      A.pushoutToQuotient :=
  rfl

private theorem endpointFlagData_ext
    {X Y : C} {S : QuillenSpan X Y}
    (A B : QuillenSpanFlagData S)
    (hKernelObj : A.kernelObj = B.kernelObj)
    (hPushoutObj : A.pushoutObj = B.pushoutObj)
    (hQuotientObj : A.quotientObj = B.quotientObj)
    (hKernelι : HEq A.kernelι B.kernelι)
    (hQuotientπ : HEq A.quotientπ B.quotientπ)
    (hSourceToPushout : HEq A.sourceToPushout B.sourceToPushout)
    (hTargetToPushout : HEq A.targetToPushout B.targetToPushout)
    (hPushoutToQuotient : HEq A.pushoutToQuotient B.pushoutToQuotient) :
    A = B := by
  cases A
  cases B
  simp_all only [QuillenSpanFlagData.mk.injEq, true_and]

/-- Reflexive endpoint flag transport is the original flag after the explicit
raw-span reflexive comparison. -/
theorem QuillenSpanFlagData.endpointTransport_refl
    {X Y : C} {S : QuillenSpan X Y} (A : QuillenSpanFlagData S) :
    QuillenSpanFlagData.transport (QuillenSpan.endpointTransportReflIso S)
        (A.endpointTransport (Iso.refl X) (Iso.refl Y)) = A := by
  apply endpointFlagData_ext <;>
    simp [QuillenSpan.endpointTransportReflIso, Span.mkIso]

/-- Direct endpoint flag transport along composite endpoint isomorphisms is
successive endpoint transport after the explicit raw-span comparison. -/
theorem QuillenSpanFlagData.endpointTransport_trans
    {X X' X'' Y Y' Y'' : C} {S : QuillenSpan X Y}
    (eX : X ≅ X') (eY : Y ≅ Y')
    (fX : X' ≅ X'') (fY : Y' ≅ Y'')
    (A : QuillenSpanFlagData S) :
    QuillenSpanFlagData.transport
        (QuillenSpan.endpointTransportTransIso S eX eY fX fY)
        (A.endpointTransport (eX.trans fX) (eY.trans fY)) =
      (A.endpointTransport eX eY).endpointTransport fX fY := by
  apply endpointFlagData_ext <;>
    simp [QuillenSpan.endpointTransportTransIso, Span.mkIso, Category.assoc]

/-- Endpoint flag transport followed by inverse endpoint transport is the
original flag after the explicit raw-span inverse comparison. -/
theorem QuillenSpanFlagData.endpointTransport_symm
    {X X' Y Y' : C} {S : QuillenSpan X Y}
    (eX : X ≅ X') (eY : Y ≅ Y') (A : QuillenSpanFlagData S) :
    QuillenSpanFlagData.transport
        (QuillenSpan.endpointTransportSymmIso S eX eY)
        ((A.endpointTransport eX eY).endpointTransport eX.symm eY.symm) =
      A := by
  apply endpointFlagData_ext <;>
    simp [QuillenSpan.endpointTransportSymmIso, Span.mkIso]

namespace QuillenSpan.EndpointIso

variable {X X' Y Y' : C} {S : QuillenSpan X Y} {T : QuillenSpan X' Y'}
variable {eX : X ≅ X'} {eY : Y ≅ Y'}

/-- A C1B endpoint-compatible apex isomorphism becomes an ordinary raw-span
isomorphism after transporting the source span endpoints. -/
noncomputable def endpointTransportIso
    (e : QuillenSpan.EndpointIso S T eX eY) :
    QuillenSpan.endpointTransport S eX eY ≅ T :=
  Span.mkIso e.1 e.hom_l e.hom_r

@[simp]
theorem endpointTransportIso_apex
    (e : QuillenSpan.EndpointIso S T eX eY) :
    Span.SpanBicat.apexIso e.endpointTransportIso = e.1 :=
  rfl

@[simp]
theorem endpointTransportIso_hom_hom
    (e : QuillenSpan.EndpointIso S T eX eY) :
    e.endpointTransportIso.hom.hom = e.1.hom :=
  rfl

@[simp]
theorem endpointTransportIso_inv_hom
    (e : QuillenSpan.EndpointIso S T eX eY) :
    e.endpointTransportIso.inv.hom = e.1.inv :=
  rfl

end QuillenSpan.EndpointIso

/-- Canonical material comparison from an endpoint-transported source flag to
a target flag under a C1B endpoint-compatible span comparison. -/
noncomputable def QuillenSpanFlagHom.endpointCanonical
    {X X' Y Y' : C} {S : QuillenSpan X Y} {T : QuillenSpan X' Y'}
    {eX : X ≅ X'} {eY : Y ≅ Y'}
    (e : QuillenSpan.EndpointIso S T eX eY)
    (A : QuillenSpanFlagData S) (B : QuillenSpanFlagData T) :
    QuillenSpanFlagData.transport e.endpointTransportIso
        (A.endpointTransport eX eY) ⟶ B :=
  QuillenSpanFlagHom.canonical _ _

end AlgebraicKTheory

end
