/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NativeKummerFlatModelsRegularSections

import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Tests for regular sections on the small étale site

The regular comparison is the specified sheafification unit. On the identity
étale object of Spec ℤ, each sheafified section comes from a unique regular function.

Source: Talpo--Vistoli, *Infinite root stacks and quasi-coherent sheaves on
logarithmic schemes*, arXiv:1410.1164v2, Definition6.10 and Remarks6.11--6.12;
Kato, *Logarithmic structures of Fontaine--Illusie*, Section1.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.NativeKummerFlatModelsRegularSections

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Opposite
open MathlibExt.AlgebraicGeometry.EtaleLogSchemes
open MathlibExt.AlgebraicGeometry.KatoChartCoefficientModels
open WantedExt.AlgebraicGeometry.NativeKummerFlatModels

example (X : Scheme.{0}) (U : X.Etale) :
    (regularIso regularSections X U).hom =
      (toSheafify X.smallEtaleTopology (rawRing X)).app (op U) := rfl

example (t : (structureRing (Spec (.of ℤ))).obj.obj
    (op (identityEtale (Spec (.of ℤ))))) :
    ∃! s : Γ(Spec (.of ℤ), ⊤),
      (regularUnit (Spec (.of ℤ)) (identityEtale (Spec (.of ℤ)))).hom (ULift.up s) = t := by
  let := regularSections.isIso (Spec (.of ℤ)) (identityEtale (Spec (.of ℤ)))
  have h := ConcreteCategory.bijective_of_isIso
    (regularUnit (Spec (.of ℤ)) (identityEtale (Spec (.of ℤ))))
  obtain ⟨s, hs⟩ := h.surjective t
  refine ⟨s.down, hs, ?_⟩
  intro u hu
  exact congrArg ULift.down (h.injective (hu.trans hs.symm))

end MathlibExtTest.AlgebraicGeometry.NativeKummerFlatModelsRegularSections
