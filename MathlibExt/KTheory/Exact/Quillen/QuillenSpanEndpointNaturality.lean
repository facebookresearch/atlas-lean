/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.KTheory.Exact.Quillen.SpanUnderlyingIsoNaturality

/-!
# Converse endpoint naturality for Quillen spans

For two raw admissible spans with isomorphic source and target endpoints, a
naturality square between their quotient classes in `QuillenQ` determines a
unique compatible isomorphism of their apices.  The converse first transports
the second span back to the endpoints of the first, then uses
`QuillenQ.mkHom_eq_iff` to recover an isomorphism of fixed-endpoint spans.

`QuillenSpan.EndpointIso` packages the exact two leg equations.  Its hom and
inverse computations, symmetry, and transitivity are exposed for downstream
shell transport.  Transitivity here composes endpoint comparisons only; this
file makes no claim about composition of spans, flagged-span coherence,
positive-degree grid fibers, contractibility, weak equivalences, or Q/S.
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

/-- A compatible isomorphism between the apices of two Quillen spans whose
source and target endpoints are identified by `eX` and `eY`. -/
def EndpointIso {X X' Y Y' : C}
    (S : QuillenSpan X Y) (T : QuillenSpan X' Y')
    (eX : X ≅ X') (eY : Y ≅ Y') :=
  { eA : S.apex ≅ T.apex //
    eA.hom ≫ T.l = S.l ≫ eX.hom ∧
      eA.hom ≫ T.r = S.r ≫ eY.hom }

namespace EndpointIso

variable {X X' X'' Y Y' Y'' : C}
variable {S : QuillenSpan X Y} {T : QuillenSpan X' Y'}
  {U : QuillenSpan X'' Y''}
variable {eX : X ≅ X'} {eY : Y ≅ Y'}
  {fX : X' ≅ X''} {fY : Y' ≅ Y''}

/-- The hom of an endpoint-compatible apex isomorphism commutes with the left
legs. -/
@[reassoc]
theorem hom_l (e : EndpointIso S T eX eY) :
    e.1.hom ≫ T.l = S.l ≫ eX.hom :=
  e.2.1

/-- The hom of an endpoint-compatible apex isomorphism commutes with the right
legs. -/
@[reassoc]
theorem hom_r (e : EndpointIso S T eX eY) :
    e.1.hom ≫ T.r = S.r ≫ eY.hom :=
  e.2.2

/-- The inverse of an endpoint-compatible apex isomorphism commutes with the
left legs in the reverse direction. -/
@[reassoc]
theorem inv_l (e : EndpointIso S T eX eY) :
    e.1.inv ≫ S.l = T.l ≫ eX.inv := by
  apply (cancel_mono eX.hom).1
  calc
    (e.1.inv ≫ S.l) ≫ eX.hom =
        e.1.inv ≫ (S.l ≫ eX.hom) := Category.assoc _ _ _
    _ = e.1.inv ≫ (e.1.hom ≫ T.l) :=
      congrArg (fun f => e.1.inv ≫ f) e.hom_l.symm
    _ = (e.1.inv ≫ e.1.hom) ≫ T.l := (Category.assoc _ _ _).symm
    _ = T.l := by rw [e.1.inv_hom_id, Category.id_comp]
    _ = (T.l ≫ eX.inv) ≫ eX.hom := by
      rw [Category.assoc, eX.inv_hom_id, Category.comp_id]

/-- The inverse of an endpoint-compatible apex isomorphism commutes with the
right legs in the reverse direction. -/
@[reassoc]
theorem inv_r (e : EndpointIso S T eX eY) :
    e.1.inv ≫ S.r = T.r ≫ eY.inv := by
  apply (cancel_mono eY.hom).1
  calc
    (e.1.inv ≫ S.r) ≫ eY.hom =
        e.1.inv ≫ (S.r ≫ eY.hom) := Category.assoc _ _ _
    _ = e.1.inv ≫ (e.1.hom ≫ T.r) :=
      congrArg (fun f => e.1.inv ≫ f) e.hom_r.symm
    _ = (e.1.inv ≫ e.1.hom) ≫ T.r := (Category.assoc _ _ _).symm
    _ = T.r := by rw [e.1.inv_hom_id, Category.id_comp]
    _ = (T.r ≫ eY.inv) ≫ eY.hom := by
      rw [Category.assoc, eY.inv_hom_id, Category.comp_id]

/-- Reflexive endpoint compatibility for a Quillen span. -/
def refl (S : QuillenSpan X Y) :
    EndpointIso S S (Iso.refl X) (Iso.refl Y) :=
  ⟨Iso.refl _, by simp, by simp⟩

/-- Reverse an endpoint-compatible apex isomorphism. -/
def symm (e : EndpointIso S T eX eY) :
    EndpointIso T S eX.symm eY.symm :=
  ⟨e.1.symm, e.inv_l, e.inv_r⟩

/-- Compose two endpoint-compatible apex isomorphisms.  This composes
comparisons of fixed raw spans, not the spans themselves. -/
def trans (e : EndpointIso S T eX eY)
    (f : EndpointIso T U fX fY) :
    EndpointIso S U (eX.trans fX) (eY.trans fY) := by
  refine ⟨e.1.trans f.1, ?_, ?_⟩
  · change (e.1.hom ≫ f.1.hom) ≫ U.l =
      S.l ≫ (eX.hom ≫ fX.hom)
    rw [Category.assoc, f.hom_l, ← Category.assoc, e.hom_l,
      Category.assoc]
  · change (e.1.hom ≫ f.1.hom) ≫ U.r =
      S.r ≫ (eY.hom ≫ fY.hom)
    rw [Category.assoc, f.hom_r, ← Category.assoc, e.hom_r,
      Category.assoc]

/-- Endpoint-compatible apex isomorphisms are unique.  The target span's
admissible-monomorphism right leg is enough to cancel their homs. -/
instance : Subsingleton (EndpointIso S T eX eY) where
  allEq e f := by
    apply Subtype.ext
    apply Iso.ext
    let _ : Mono T.r :=
      (show IsAdmissibleMono T.r from T.wr).mono
    apply (cancel_mono T.r).1
    exact e.hom_r.trans f.hom_r.symm

/-- Explicit uniqueness theorem for endpoint-compatible apex isomorphisms. -/
theorem unique (e f : EndpointIso S T eX eY) : e = f :=
  Subsingleton.elim _ _

end EndpointIso

end QuillenSpan

/-- Transport a Quillen span backwards along endpoint isomorphisms, retaining
its apex and composing its legs with the inverse endpoint maps. -/
private def quillenSpanEndpointBackTransport
    {X X' Y Y' : C} (T : QuillenSpan X' Y')
    (eX : X ≅ X') (eY : Y ≅ Y') :
    QuillenSpan X Y where
  apex := T.apex
  l := T.l ≫ eX.inv
  r := T.r ≫ eY.inv
  wl := admissibleEpi_comp.comp_mem _ _ T.wl
    (IsAdmissibleEpi.of_isIso _)
  wr := admissibleMono_comp.comp_mem _ _ T.wr
    (IsAdmissibleMono.of_isIso _)

/-- Converse endpoint naturality: a quotient-level naturality square between
two raw Quillen spans determines a compatible isomorphism of their apices. -/
theorem QuillenQ.endpointIso_nonempty_of_mkHom_naturality
    {X X' Y Y' : C}
    (S : QuillenSpan X Y) (T : QuillenSpan X' Y')
    (eX : X ≅ X') (eY : Y ≅ Y')
    (h : QuillenQ.mkHom S ≫ (QuillenQ.underlyingIso eY).hom =
      (QuillenQ.underlyingIso eX).hom ≫ QuillenQ.mkHom T) :
    Nonempty (QuillenSpan.EndpointIso S T eX eY) := by
  let R : QuillenSpan X Y :=
    quillenSpanEndpointBackTransport T eX eY
  have hR :
      QuillenQ.mkHom R ≫ (QuillenQ.underlyingIso eY).hom =
        (QuillenQ.underlyingIso eX).hom ≫ QuillenQ.mkHom T := by
    apply QuillenQ.mkHom_naturality_of_span_iso
      R T eX eY (Iso.refl T.apex)
    · simp [R, quillenSpanEndpointBackTransport, Category.assoc]
    · simp [R, quillenSpanEndpointBackTransport, Category.assoc]
  have hSR : QuillenQ.mkHom S = QuillenQ.mkHom R := by
    apply (cancel_mono (QuillenQ.underlyingIso eY).hom).1
    exact h.trans hR.symm
  obtain ⟨E⟩ := QuillenQ.mkHom_eq_iff.mp hSR
  refine ⟨⟨Span.SpanBicat.apexIso E, ?_, ?_⟩⟩
  · apply (cancel_mono eX.inv).1
    change (E.hom.hom ≫ T.l) ≫ eX.inv =
      (S.l ≫ eX.hom) ≫ eX.inv
    simpa only [R, quillenSpanEndpointBackTransport, Category.assoc,
      eX.hom_inv_id, Category.comp_id] using E.hom.hom_l
  · apply (cancel_mono eY.inv).1
    change (E.hom.hom ≫ T.r) ≫ eY.inv =
      (S.r ≫ eY.hom) ≫ eY.inv
    simpa only [R, quillenSpanEndpointBackTransport, Category.assoc,
      eY.hom_inv_id, Category.comp_id] using E.hom.hom_r

/-- A selected endpoint-compatible apex isomorphism supplied by converse
endpoint naturality.  Its leg computations are
`QuillenSpan.EndpointIso.hom_l`, `hom_r`, `inv_l`, and `inv_r`. -/
noncomputable def QuillenQ.endpointIsoOfMkHomNaturality
    {X X' Y Y' : C}
    (S : QuillenSpan X Y) (T : QuillenSpan X' Y')
    (eX : X ≅ X') (eY : Y ≅ Y')
    (h : QuillenQ.mkHom S ≫ (QuillenQ.underlyingIso eY).hom =
      (QuillenQ.underlyingIso eX).hom ≫ QuillenQ.mkHom T) :
    QuillenSpan.EndpointIso S T eX eY :=
  Classical.choice
    (QuillenQ.endpointIso_nonempty_of_mkHom_naturality S T eX eY h)

end AlgebraicKTheory

end
