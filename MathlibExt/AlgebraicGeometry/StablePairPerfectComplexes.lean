/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StablePairFamilies
public import MathlibExt.AlgebraicGeometry.StablePairInternalHomMaps

/-!
# Native finite-perfect-complex endomorphisms

Every degree is the finite product of actual sheaf internal Homs.
The differential is postcomposition with d_A minus the degree's native
Koszul sign times precomposition with d_A. Both maps are the actual
localized module maps. The squared-zero proof is an explicit generic
dependency of this fixed differential, rather than a chosen operator.

A stable-pair resolution is an actual finite locally free cochain
complex with a quasi-isomorphism to the native pair complex.

Reference: Pandharipande–Thomas, arXiv:0707.2348v5, §2.3,
the finite locally free resolution preceding Lemma 2.10.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StablePairPerfectComplexes

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open CoherentCurveLinearSeries BundleTrace StablePairInternalHomMaps
open StablePairFamilies
attribute [local instance] HasDerivedCategory.standard

/-- Actual local finite freeness, allowing rank to vary among components. -/
def LocallyFiniteFree {Y : Scheme} (E : Y.Modules) : Prop :=
  ∀ y : Y, ∃ (U : Y.Opens) (r : ℕ), y ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj E ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin r))

structure FiniteComplex (Y : Scheme) where
  cochain : CochainComplex Y.Modules ℤ
  lower : ℤ
  upper : ℤ
  outside : ∀ i : ℤ, i < lower ∨ upper < i → IsZero (cochain.X i)
  locallyfree : ∀ i, LocallyFiniteFree (cochain.X i)

variable {Y : Scheme} (A : FiniteComplex Y)

abbrev Indices := {i : ℤ // i ∈ Finset.Icc A.lower A.upper}

/-- The actual finite sheaf-Hom source in degree n. -/
@[implicit_reducible]
def endDegree (n : ℤ) : Y.Modules :=
  ∏ᶜ fun i : Indices A => homSheaf Y (A.cochain.X i.val) (A.cochain.X (i.val+n))

/-- The precomposition term of the genuine dg differential, including the upper boundary. -/
def preTerm (n : ℤ) (i : Indices A) :
    endDegree A n ⟶ homSheaf Y (A.cochain.X i.val) (A.cochain.X (i.val+(n+1))) :=
  if h : i.val + 1 ∈ Finset.Icc A.lower A.upper then
    Pi.π (fun j : Indices A =>
      homSheaf Y (A.cochain.X j.val) (A.cochain.X (j.val+n))) ⟨i.val+1,h⟩ ≫
      precompose (A.cochain.d i.val (i.val+1)) ≫
        postcompose
          (A.cochain.XIsoOfEq (p := i.val+1+n) (q := i.val+(n+1)) (by omega)).hom
  else 0

/-- The fixed d_Hom(φ)=d_Aφ−(−1)^nφd_A source map. -/
def endDifferential (n : ℤ) : endDegree A n ⟶ endDegree A (n+1) :=
  Pi.lift (fun i : Indices A =>
    let post : endDegree A n ⟶
        homSheaf Y (A.cochain.X i.val) (A.cochain.X (i.val+(n+1))) :=
      Pi.π (fun j : Indices A =>
        homSheaf Y (A.cochain.X j.val) (A.cochain.X (j.val+n))) i ≫
          postcompose (A.cochain.d (i.val+n) (i.val+(n+1)))
    post - (Int.negOnePow n).val • preTerm A n i)

def EndSquaredZero : Prop :=
  ∀ n : ℤ, endDifferential A n ≫ endDifferential A (n+1) = 0

/-- The dg endomorphism complex is constructed from that particular differential. -/
def endComplex (h : EndSquaredZero A) : CochainComplex Y.Modules ℤ :=
  CochainComplex.of (endDegree A) (endDifferential A) h

/-- A perfect representative of the actual universal-pair complex. -/
structure PairResolution {X T : Over (Spec (.of ℂ))} (F : StablePairFamilies.RawPair X T)
    extends FiniteComplex (StablePairFamilies.total X T) where
  comparison : cochain ⟶ StablePairFamilies.complex F
  [quasiIso : QuasiIso comparison]

attribute [instance] PairResolution.quasiIso

end MathlibExt.AlgebraicGeometry.StablePairPerfectComplexes
