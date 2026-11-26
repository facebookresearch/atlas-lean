/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AffinoidTorsorAlgebraizationModels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Fpqc restriction preserves torsors

Restriction along each actual scheme map preserves the native fpqc torsor
condition: the over-map pullback of a torsor action sheaf is a torsor.

Source: Fargues--Scholze arXiv:2102.13459v4, Section III.3 and VI.1;
Stacks Project, Tags03AG and04UV; affinoid algebraization.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AffinoidTorsorAlgebraization

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.AlgebraicGeometry
open MathlibExt.CategoryTheory.SheafTorsorGroupoids
open WittDiscTorsorModels AffinoidTorsorAlgebraizationModels

/-- Sections of the terminal sheaf over an over-site are unique. -/
private instance unique_terminalSections (E : Type) [Field E]
    (X : Over (Spec (.of E))) (T : (Over X)ᵒᵖ) :
    Unique ((⊤_ (Sheaf (topology E X) (Type 1))).obj.obj T) := by
  have hPresSh : IsTerminal ((sheafToPresheaf (topology E X) (Type 1)).obj
      (⊤_ (Sheaf (topology E X) (Type 1)))) :=
    IsTerminal.isTerminalObj _ _ terminalIsTerminal
  have hT : IsTerminal ((⊤_ (Sheaf (topology E X) (Type 1))).obj.obj T) :=
    IsTerminal.isTerminalObj ((evaluation (Over X)ᵒᵖ (Type 1)).obj T) _ hPresSh
  exact (Types.isTerminalEquivUnique _) hT

/-- Restriction along each actual scheme map preserves the native fpqc torsor condition. -/
public theorem fpqcRestrictionPreservesTorsors
    (E : Type) [Field E] (G : Over (Spec (.of E))) [GrpObj G]
    {B C : Over (Spec (.of E))} (f : B ⟶ C) : FpqcPreservesTorsors E G f := by
  intro N hN
  constructor
  · have hEpi : Epi (terminal.from N.sheaf) := hN.1
    have hLS : Sheaf.IsLocallySurjective (terminal.from N.sheaf) :=
      (Sheaf.isLocallySurjective_iff_epi _).mpr hEpi
    rw [← Sheaf.isLocallySurjective_iff_epi]
    constructor
    intro U s
    obtain ⟨star⟩ := (inferInstance : Nonempty
      ((⊤_ (Sheaf (topology E C) (Type 1))).obj.obj (op ((Over.map f).obj U))))
    have hR : Presheaf.imageSieve (terminal.from N.sheaf).hom star ∈
        (topology E C) ((Over.map f).obj U) :=
      Presheaf.imageSieve_mem _ _ _
    have hPb := Functor.cover_lift (Over.map f) (topology E B) (topology E C) hR
    apply (topology E B).superset_covering _ hPb
    intro V i hi
    obtain ⟨t, -⟩ := hi
    exact ⟨t, Subsingleton.elim _ _⟩
  · have hI : IsIso (actionPair (topology E C) (groupSheaf E G C) N) := hN.2
    have heq : actionPair (topology E B) (groupSheaf E G B)
        ((actionPullback G f).obj N)
        = Functor.whiskerLeft (Over.map f).op
          (actionPair (topology E C) (groupSheaf E G C) N) := rfl
    rw [heq]
    exact Functor.isIso_whiskerLeft _ _

end WantedExt.AlgebraicGeometry.AffinoidTorsorAlgebraization
