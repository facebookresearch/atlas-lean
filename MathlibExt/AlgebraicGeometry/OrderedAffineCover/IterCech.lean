/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicGeometry_IterCech.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.AlgebraicGeometry.OrderedAffineCover.BiCech

/-!
# Restriction maps into the iterated Čech complex

Given ordered open families `𝔄`, `𝔅`, `ℭ` of a scheme and a presheaf of modules `F`, the
iterated Čech complex has `(r, m)` term
`IterCech.C F 𝔄 𝔅 ℭ r m = ∏_{K ∈ ℭ.Idx r} Tot(biCech F 𝔄 (𝔅 ∩ ℭ.inter K)) m`.
This file defines these terms and two restriction maps into them:

* `IterCech.augTot`: from the total complex of `biCech F 𝔄 𝔅` into the column `r = 0`, by
  restricting to each `𝔅 ∩ ℭ.U k`;
* `IterCech.augCech`: from the Čech cochains of `F` on an ordered affine cover `ℭ'` into the
  row `m = 0`, by restricting each section to the relevant intersections.

The names follow the source, where these maps are the augmentations of the iterated Čech
complex; its differentials are not defined here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

namespace Scheme.OrderedOpenFamily

variable {Z : Scheme.{u}} (𝔅 : Z.OrderedOpenFamily)

/-- The family `{𝔅.U j ⊓ W}` obtained by intersecting with a fixed open `W`. -/
def restr (W : Z.Opens) : Z.OrderedOpenFamily where
  ι := 𝔅.ι
  U j := 𝔅.U j ⊓ W

theorem restr_ι (W : Z.Opens) : (𝔅.restr W).ι = 𝔅.ι := rfl

theorem restr_U (W : Z.Opens) (j : 𝔅.ι) : (𝔅.restr W).U j = 𝔅.U j ⊓ W := rfl

theorem restr_inter_le (W : Z.Opens) {q : ℕ} (t : 𝔅.Idx q) :
    (𝔅.restr W).inter (show (𝔅.restr W).Idx q from t) ≤ 𝔅.inter t ⊓ W :=
  le_inf (le_iInf fun j => (iInf_le _ j).trans inf_le_left) ((iInf_le _ 0).trans inf_le_right)

theorem le_restr_inter (W : Z.Opens) {q : ℕ} (t : 𝔅.Idx q) :
    𝔅.inter t ⊓ W ≤ (𝔅.restr W).inter (show (𝔅.restr W).Idx q from t) :=
  le_iInf fun j => inf_le_inf_right _ (iInf_le _ j)

end Scheme.OrderedOpenFamily

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {π : Z ⟶ Spec (.of R)}
  (F : OModulePresheaf π)
variable (𝔄 𝔅 ℭ : Z.OrderedOpenFamily)

namespace IterCech

/-- The `(r, m)` term of the iterated Čech complex: over each `r`-simplex `K` of `ℭ`, the
degree `m` total cochains of the Čech double complex of `𝔄` and `𝔅 ∩ ℭ.inter K`. -/
abbrev C (r m : ℕ) : Type u :=
  ∀ K : ℭ.Idx r, DoubleComplex.Tot (F.biCech 𝔄 (𝔅.restr (ℭ.inter K))) m

/-- Restriction of Čech double cochains from `𝔅` to `𝔅 ∩ W`. -/
def resC₀ (W : Z.Opens) (p q : ℕ) :
    BiCech.C F 𝔄 𝔅 p q →ₗ[R] BiCech.C F 𝔄 (𝔅.restr W) p q where
  toFun c := fun st =>
    F.res (inf_le_inf_left _ (le_trans (𝔅.restr_inter_le W st.2) inf_le_left)) (c st)
  map_add' c c' := funext fun _ => map_add (F.res _) (c _) (c' _)
  map_smul' a c := funext fun _ => LinearMap.map_smul (F.res _) a (c _)

theorem resC₀_apply (W : Z.Opens) (p q : ℕ) (c : BiCech.C F 𝔄 𝔅 p q)
    (st : 𝔄.Idx p × (𝔅.restr W).Idx q) :
    resC₀ F 𝔄 𝔅 W p q c st =
      F.res (inf_le_inf_left _ (le_trans (𝔅.restr_inter_le W st.2) inf_le_left)) (c st) :=
  rfl

/-- Restriction of total cochains from `𝔅` to `𝔅 ∩ W`. -/
def resTot₀ (W : Z.Opens) (m : ℕ) :
    DoubleComplex.Tot (F.biCech 𝔄 𝔅) m →ₗ[R] DoubleComplex.Tot (F.biCech 𝔄 (𝔅.restr W)) m :=
  LinearMap.pi fun pq => (resC₀ F 𝔄 𝔅 W pq.1.1 pq.1.2).comp (LinearMap.proj pq)

theorem resTot₀_apply (W : Z.Opens) (m : ℕ) (c : DoubleComplex.Tot (F.biCech 𝔄 𝔅) m)
    (pq : DoubleComplex.Diag m) (st : 𝔄.Idx pq.1.1 × (𝔅.restr W).Idx pq.1.2) :
    resTot₀ F 𝔄 𝔅 W m c pq st =
      F.res (inf_le_inf_left _ (le_trans (𝔅.restr_inter_le W st.2) inf_le_left)) (c pq st) :=
  rfl

/-- The restriction map from the degree-`m` total cochains of the Čech double complex of `𝔄` and
`𝔅` to the `(0, m)` term of the iterated Čech complex: over each `0`-simplex `K` of `ℭ`, it
restricts every component from `𝔅` to `𝔅 ∩ ℭ.inter K`. -/
def augTot (m : ℕ) : DoubleComplex.Tot (F.biCech 𝔄 𝔅) m →ₗ[R] C F 𝔄 𝔅 ℭ 0 m :=
  LinearMap.pi fun K => resTot₀ F 𝔄 𝔅 (ℭ.inter K) m

theorem augTot_apply (m : ℕ) (c : DoubleComplex.Tot (F.biCech 𝔄 𝔅) m) (K : ℭ.Idx 0) :
    augTot F 𝔄 𝔅 ℭ m c K = resTot₀ F 𝔄 𝔅 (ℭ.inter K) m c := rfl

/-- The restriction map from the degree-`r` Čech cochains of `F` on an ordered affine cover `ℭ'`
to the `(r, 0)` term of the iterated Čech complex: over each `r`-simplex `K` of `ℭ'`, it restricts
the value of a cochain at `K` to each open `𝔄.inter s ⊓ (𝔅 ∩ ℭ'.inter K).inter t`. -/
def augCech (ℭ' : Z.OrderedAffineCover) (r : ℕ) :
    F.cochain ℭ' r →ₗ[R] C F 𝔄 𝔅 ℭ'.toOpenFamily r 0 where
  toFun x := fun K _ st =>
    F.res (show 𝔄.inter st.1 ⊓ (𝔅.restr (ℭ'.toOpenFamily.inter K)).inter st.2 ≤ ℭ'.inter K from
        le_trans inf_le_right (le_trans (𝔅.restr_inter_le _ st.2) inf_le_right))
      (x K)
  map_add' x x' := funext fun K => funext fun _ => funext fun _ => map_add (F.res _) (x K) (x' K)
  map_smul' a x := funext fun K => funext fun _ => funext fun _ =>
    LinearMap.map_smul (F.res _) a (x K)

theorem augCech_apply (ℭ' : Z.OrderedAffineCover) (r : ℕ) (x : F.cochain ℭ' r)
    (K : ℭ'.toOpenFamily.Idx r) (pq : DoubleComplex.Diag 0)
    (st : 𝔄.Idx pq.1.1 × (𝔅.restr (ℭ'.toOpenFamily.inter K)).Idx pq.1.2) :
    augCech F 𝔄 𝔅 ℭ' r x K pq st
      = F.res (show 𝔄.inter st.1 ⊓ (𝔅.restr (ℭ'.toOpenFamily.inter K)).inter st.2 ≤
          ℭ'.inter K from
          le_trans inf_le_right (le_trans (𝔅.restr_inter_le _ st.2) inf_le_right)) (x K) := rfl

end IterCech

end OModulePresheaf

end AlgebraicGeometry
