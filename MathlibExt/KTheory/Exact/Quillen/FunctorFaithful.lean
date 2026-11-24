/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.KTheory.Exact.Quillen.Functor
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Faithfulness of exact functors on the original Quillen category

An additive, full, faithful exact functor between exact categories induces a
faithful map of the original Quillen categories. The actual mapped apex
isomorphisms and both leg equations reflect every quotient equality. Neither
category needs an abelian structure or an additional exactness-reflection
certificate, and all four universe roles remain independent.
-/

public section
noncomputable section

open CategoryTheory Limits CategoryTheory.ExactCategory

universe uA vA uB vB

namespace AlgebraicKTheory

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
  [HasZeroObject A] [HasBinaryBiproducts A] [ExactCategory A]
  {B : Type uB} [Category.{vB} B] [Preadditive B]
  [HasZeroObject B] [HasBinaryBiproducts B] [ExactCategory B]

private def originalMappedSpanIsoPreimage (F : A ⥤ B)
    [F.Additive] [F.Full] [F.Faithful] [F.IsExact]
    {a b : A} {S T : QuillenSpan a b}
    (e : QuillenSpan.map F S ≅ QuillenSpan.map F T) : S ≅ T := by
  rw [QuillenSpan.map_eq_raw F S, QuillenSpan.map_eq_raw F T] at e
  let apexIso : F.obj S.apex ≅ F.obj T.apex := Span.SpanBicat.apexIso e
  refine Span.mkIso (F.preimageIso apexIso) ?_ ?_
  · apply F.map_injective
    change F.map (F.preimage apexIso.hom ≫ T.l) = F.map S.l
    rw [F.map_comp, F.map_preimage]
    exact e.hom.hom_l
  · apply F.map_injective
    change F.map (F.preimage apexIso.hom ≫ T.r) = F.map S.r
    rw [F.map_comp, F.map_preimage]
    exact e.hom.hom_r

private theorem originalQMapInjective (F : A ⥤ B)
    [F.Additive] [F.Full] [F.Faithful] [F.IsExact]
    {a b : A} (f g : (⟨a⟩ : QuillenQ A) ⟶ ⟨b⟩)
    (h : (QuillenQ.map F).map f = (QuillenQ.map F).map g) : f = g := by
  revert h
  refine Quotient.inductionOn f ?_
  intro S h
  revert h
  refine Quotient.inductionOn g ?_
  intro T h
  change (QuillenQ.map F).map (QuillenQ.mkHom S) =
    (QuillenQ.map F).map (QuillenQ.mkHom T) at h
  rw [QuillenQ.map_mk, QuillenQ.map_mk] at h
  obtain ⟨e⟩ := (QuillenQ.mkHom_eq_iff).mp h
  exact QuillenQ.mkHom_sound (originalMappedSpanIsoPreimage F e)

/-- Faithfulness of the original Q-map is derived by reflecting the actual
mapped apex isomorphism and both leg equations. -/
theorem QuillenQ.map_faithful (F : A ⥤ B)
    [F.Additive] [F.Full] [F.Faithful] [F.IsExact] : (QuillenQ.map F).Faithful where
  map_injective {X Y} f g h := by
    obtain ⟨a⟩ := X
    obtain ⟨b⟩ := Y
    exact originalQMapInjective F f g h

end AlgebraicKTheory
