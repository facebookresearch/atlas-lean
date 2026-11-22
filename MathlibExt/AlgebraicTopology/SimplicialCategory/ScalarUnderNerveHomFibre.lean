/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarUnderNerveProjection
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# The SAME whole original Hom is the actual scalar under-nerve vertex fibre

The native pullback of the SAME original projection along its actual
point map has the full original Hom simplicial set as its genuine fibre.
The forward map retains every original coefficient as its entire native
constant undercategory word. The whole inverse is obtained from actual
all-arity chain recognition and the native evaluated pullback. Every
original scalar operator and projection is retained; no homotopy-fibre
or group-completion weak theorem is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.ScalarUnderCategory

variable (C : CategoryTheory.SimplicialEnrichment.Carrier.{u})

/-- Every actual coefficient of the SAME original point map is its full constant original base word. -/
theorem point_apply (y : C) (q : SimplexCategoryᵒᵖ) (a : (Δ[0] : SSet.{u}).obj q) :
    (point C y).app q a = (Functor.const (Fin (q.unop.len + 1))).obj (sourceObject C y q) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro i j f
  apply heq_of_eq
  exact (scalarOperator (C := C) (SimplexCategory.const q.unop ⦋0⦌ 0).op).map_id (sourceObject C y (op ⦋0⦌))

/-- The SAME full original Hom map has the exact actual original vertex-fibre projection square. -/
theorem homInclusion_projection (z y : C) : homInclusion C z y ≫ projection C z =
    stdSimplex.isTerminalObj₀.from (z ⟶[SSet.{u}] y) ≫ point C y := by
  ext q a
  exact (projection_homInclusion_apply C z y q a).trans
    (point_apply C y q ((stdSimplex.isTerminalObj₀.from (z ⟶[SSet.{u}] y)).app q a)).symm

/-- Every full original coefficient is recovered uniquely from its SAME native constant undercategory word. -/
theorem homInclusion_app_injective (z y : C) (q : SimplexCategoryᵒᵖ) :
    Function.Injective ((homInclusion C z y).app q) := by
  intro a b h
  have h₀ := Functor.congr_obj h 0
  change Under.mk (X := sourceObject C z q) (Y := sourceObject C y q) a =
    Under.mk (X := sourceObject C z q) (Y := sourceObject C y q) b at h₀
  injection h₀ with h₁ h₂ h₃

private theorem point_degree_subsingleton (q : SimplexCategoryᵒᵖ) :
    Subsingleton ((Δ[0] : SSet.{u}).obj q) := by
  have : Subsingleton (q.unop ⟶ ⦋0⦌) := ⟨SimplexCategory.isTerminalZero.hom_ext⟩
  change Subsingleton (ULift.{u} (q.unop ⟶ ⦋0⦌))
  infer_instance

/-- The SAME native whole Hom inclusion is monic, retaining all original scalar degrees. -/
instance homInclusion_mono (z y : C) : Mono (homInclusion C z y) := by
  have (q : SimplexCategoryᵒᵖ) : Mono ((homInclusion C z y).app q) :=
    (mono_iff_injective _).mpr (homInclusion_app_injective C z y q)
  exact NatTrans.mono_of_mono_app _

/-- The literal original vertex fibre of the SAME full under-nerve diagonal projection. -/
abbrev vertexFibre (z y : C) : SSet.{u} := pullback (projection C z) (point C y)

/-- Every SAME original full Hom simplex is mapped to the actual native projection fibre by its complete original
constant word. -/
def homToFibre (z y : C) : (z ⟶[SSet.{u}] y) ⟶ vertexFibre C z y :=
  pullback.lift (homInclusion C z y) (stdSimplex.isTerminalObj₀.from _) (homInclusion_projection C z y)

/-- The entire forward original fibre comparison retains its exact full original under-word map. -/
theorem homToFibre_fst (z y : C) : homToFibre C z y ≫ pullback.fst _ _ = homInclusion C z y :=
  pullback.lift_fst _ _ _

/-- The actual full forward fibre comparison retains its SAME original point coefficient map. -/
theorem homToFibre_snd (z y : C) : homToFibre C z y ≫ pullback.snd _ _ = stdSimplex.isTerminalObj₀.from _ :=
  pullback.lift_snd _ _ _

/-- The SAME complete original Hom comparison is an actual Iso onto the full native vertex fibre. -/
instance homToFibre_isIso (z y : C) : IsIso (homToFibre C z y) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro q
  rw [isIso_iff_bijective]
  have hfst := congrArg (fun f => f.app q) (homToFibre_fst C z y)
  refine ⟨?_, ?_⟩
  · intro a b h
    apply homInclusion_app_injective C z y q
    exact (congr($(hfst) a)).symm.trans
      ((congrArg (fun x => (pullback.fst (projection C z) (point C y)).app q x) h).trans (congr($(hfst) b)))
  · intro a
    let E := (CategoryTheory.evaluation SimplexCategoryᵒᵖ (Type u)).obj q
    have : Subsingleton (E.obj (Δ[0] : SSet.{u})) := point_degree_subsingleton q
    have hpb := (IsPullback.of_hasPullback (projection C z) (point C y)).map E
    have hp := congr($(pullback.condition (f := projection C z) (g := point C y)).app q a)
    have he : (projection C z).app q ((pullback.fst (projection C z) (point C y)).app q a) =
        (Functor.const (Fin (q.unop.len + 1))).obj (sourceObject C y q) :=
      hp.trans (point_apply C y q ((pullback.snd (projection C z) (point C y)).app q a))
    obtain ⟨b, hb⟩ := (projection_eq_const_iff C z y q _).mp he
    refine ⟨b, Types.ext_of_isPullback hpb ?_ ?_⟩
    · exact (congr($(hfst) b)).trans hb
    · exact Subsingleton.elim _ _

/-- Both entire original maps identify the SAME full original Hom simplicial set with the actual native vertex
pullback fibre. -/
def homFibreIso (z y : C) : (z ⟶[SSet.{u}] y) ≅ vertexFibre C z y := asIso (homToFibre C z y)

end SSet.ScalarUnderCategory
