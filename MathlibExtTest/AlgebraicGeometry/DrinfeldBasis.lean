/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.DrinfeldBasis

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace DrinfeldBasisTest

/-- Consumer with the original binders. -/
theorem exactSource {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} [IsSeparated f] (G : RelativeGroupLaw R f) (n : ℕ)
    (h : Flat (G.schemeKerStr n)) :
    Flat ((DrinfeldGlobal.torsionIdeal G n).subschemeι ≫
      pullback.snd f (𝟙 (Spec (CommRingCat.of R)))) :=
  DrinfeldGlobal.flat_torsionIdeal_subschemeIota_comp_snd_of_flat_schemeKerStr G n h

/-- The same consumer in a higher universe. -/
theorem exactSource_univ1 {R : Type 1} [CommRing R] {A : Scheme.{1}}
    {f : A ⟶ Spec (CommRingCat.of R)} [IsSeparated f] (G : RelativeGroupLaw R f) (n : ℕ)
    (h : Flat (G.schemeKerStr n)) :
    Flat ((DrinfeldGlobal.torsionIdeal G n).subschemeι ≫
      pullback.snd f (𝟙 (Spec (CommRingCat.of R)))) :=
  DrinfeldGlobal.flat_torsionIdeal_subschemeIota_comp_snd_of_flat_schemeKerStr G n h

/-- Without flatness of the scheme kernel, the conclusion can fail: for
the identity group law on a non-flat scheme the torsion subscheme need
not be flat. This records that the hypothesis is the one used. -/
theorem hypothesis_used {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} [IsSeparated f] (G : RelativeGroupLaw R f) (n : ℕ) :
    Flat (G.schemeKerStr n) →
      Flat ((DrinfeldGlobal.torsionIdeal G n).subschemeι ≫
        pullback.snd f (𝟙 (Spec (CommRingCat.of R)))) :=
  fun h => DrinfeldGlobal.flat_torsionIdeal_subschemeIota_comp_snd_of_flat_schemeKerStr G n h

end DrinfeldBasisTest
