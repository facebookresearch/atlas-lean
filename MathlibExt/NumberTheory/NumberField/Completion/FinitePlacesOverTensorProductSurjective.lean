/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.Completion.FinitePlacesOverTensorProduct
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Surjectivity of the finite-place completion tensor product map

For a number field extension `L / K` and a finite place `v` of `K`, the canonical
`v.adicCompletion K`-algebra map `completionTensorProductMap v` into the product of the
`w`-adic completions over all places `w` of `L` above `v` is surjective.

The proof is by weak approximation for the pairwise inequivalent finite-place absolute
values, transported to the completions along isometric coordinate maps, so the diagonal
map out of `L` is dense; precomposing with `y ↦ 1 ⊗ₜ y` makes the tensor product map
dense, and its range is finite-dimensional over `v.adicCompletion K`, hence closed.

## ATLAS source correspondence

This is the surjectivity clause of ATLAS NumberTheoryI N265, Theorem 13.5.
At atlas-lean commit `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, the theorem is indexed in
[`v1/Atlas/NumberTheoryI/targets.yaml`, lines 1873--1879](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L1873-L1879),
and the finite-place map is
[`GlobalFields.canonicalMap_finite`, lines 726--738](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L726-L738).
Its source surjectivity result is
[`canonicalMap_finite_surjective_by_approx`, lines 983--1023](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L983-L1023)
(and the later wrapper at
[lines 1088--1138](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L1088-L1138)).
The map is the same one
constructed as `completionTensorProductMap` in the preceding stage, up to the
documented canonical swap from `L ⊗[K] K_v` to `K_v ⊗[K] L`, with the same
dependent product over `w ∣ v` and the same chosen completion maps.

The source proof obtains surjectivity from a finite-dimensional dimension
equality plus injectivity; that injectivity passes through the admission-backed
[`canonicalMap_finite_ker_eq_bot` at lines 978--981](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/GlobalFields.lean#L978-L981).
This module replaces only
that proof route, not the statement:

* `denseRange_algebraMap_placesOver` applies weak approximation to the
  pairwise inequivalent normalized `w`-adic absolute values and transports the
  dense diagonal image of `L` into `∏_{w ∣ v} L_w` through isometric completion
  maps;
* `denseRange_completionTensorProductMap` factors that diagonal map through
  `y ↦ 1 ⊗ₜ y`, proving the source canonical tensor map has dense range; and
* `completionTensorProductMap_surjective` observes that its linear range is
  finite-dimensional over `K_v`, hence closed. A dense closed subspace is the
  whole target, yielding exactly the source surjectivity conclusion.

This proves no injectivity or equivalence claim; those remain separate stages
of N265.
-/

@[expose] public section

namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField Valued
open scoped IsDedekindDomain.HeightOneSpectrum.CompletionTensorProduct
open scoped NumberField.LiesOver
open TensorProduct

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K))

omit [NumberField K] in
private theorem adicAbv_nontrivial (w : v.placesOver L) :
    (NumberField.HeightOneSpectrum.adicAbv L w.val).IsNontrivial := by
  obtain ⟨a, ha_mem, ha_ne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot w.val.ne_bot
  have ha0 : algebraMap (𝓞 L) L a ≠ 0 :=
    (FaithfulSMul.algebraMap_eq_zero_iff (𝓞 L) L).not.2 ha_ne
  refine ⟨algebraMap (𝓞 L) L a, ha0, ?_⟩
  have hlt :
      NumberField.HeightOneSpectrum.adicAbv L w.val
        (algebraMap (𝓞 L) L a) < 1 :=
    (w.val.adicAbv_coe_lt_one_iff
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal w.val) a).mpr
      ha_mem
  exact ne_of_lt hlt

omit [NumberField K] in
private theorem adicAbv_pairwise :
    Pairwise fun a b : v.placesOver L =>
      ¬(NumberField.HeightOneSpectrum.adicAbv L a.val).IsEquiv
        (NumberField.HeightOneSpectrum.adicAbv L b.val) := by
  intro a b hne hEquiv
  apply hne
  apply Subtype.ext
  apply HeightOneSpectrum.ext
  apply Ideal.ext
  intro r
  have hlt :
      ∀ x : L,
        NumberField.HeightOneSpectrum.adicAbv L a.val x < 1 ↔
          NumberField.HeightOneSpectrum.adicAbv L b.val x < 1 :=
    fun x => hEquiv.lt_one_iff
  have ha :
      NumberField.HeightOneSpectrum.adicAbv L a.val
          (algebraMap (𝓞 L) L r) < 1 ↔
      r ∈ a.val.asIdeal :=
    a.val.adicAbv_coe_lt_one_iff
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal a.val) r
  have hb :
      NumberField.HeightOneSpectrum.adicAbv L b.val
          (algebraMap (𝓞 L) L r) < 1 ↔
      r ∈ b.val.asIdeal :=
    b.val.adicAbv_coe_lt_one_iff
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal b.val) r
  rw [← ha, ← hb]
  exact hlt _

private noncomputable def coord (w : v.placesOver L) :
    WithAbs (NumberField.HeightOneSpectrum.adicAbv L w.val) →+*
      w.val.adicCompletion L :=
  (NumberField.FinitePlace.embedding w.val).comp (WithAbs.equiv _).toRingHom

omit [NumberField K] in
private theorem coord_isometry (w : v.placesOver L) :
    Isometry (coord v w) := by
  refine AddMonoidHomClass.isometry_of_norm _ (fun x => ?_)
  have h1 :
      ‖coord v w x‖ =
        NumberField.HeightOneSpectrum.adicAbv L w.val
          ((WithAbs.equiv _) x) := by
    simp only [coord, RingHom.comp_apply]
    exact NumberField.FinitePlace.norm_embedding w.val _
  have h2 :
      ‖x‖ =
        NumberField.HeightOneSpectrum.adicAbv L w.val
          ((WithAbs.equiv _) x) :=
    WithAbs.norm_eq_apply_ofAbs _ x
  rw [h1, h2]

omit [NumberField K] in
private theorem coord_comp_algebraMap (w : v.placesOver L) :
    (⇑(coord v w) ∘
        algebraMap L
          (WithAbs
            (NumberField.HeightOneSpectrum.adicAbv L w.val))) =
      algebraMap L (w.val.adicCompletion L) := by
  funext y
  simp only [coord, RingHom.comp_apply, Function.comp_apply]
  rw [NumberField.FinitePlace.embedding_apply]
  rfl

omit [NumberField K] in
private theorem coord_denseRange (w : v.placesOver L) :
    DenseRange (coord v w) := by
  apply DenseRange.of_comp
    (g := algebraMap L
      (WithAbs (NumberField.HeightOneSpectrum.adicAbv L w.val)))
  rw [coord_comp_algebraMap]
  exact w.val.denseRange_algebraMap L

private theorem weakApprox :
    DenseRange
      (algebraMap L
        ((w : v.placesOver L) →
          WithAbs (NumberField.HeightOneSpectrum.adicAbv L w.val))) :=
  AbsoluteValue.denseRange_algebraMap_pi (fun w => adicAbv_nontrivial v w)
    (adicAbv_pairwise v)

theorem denseRange_algebraMap_placesOver :
    DenseRange (fun y : L => fun w : v.placesOver L =>
      algebraMap L (w.val.adicCompletion L) y) := by
  have hWA := weakApprox (K := K) (L := L) v
  have hPi :=
    DenseRange.piMap (fun w : v.placesOver L => coord_denseRange v w)
  have hcont :=
    Continuous.piMap
      (fun w : v.placesOver L => (coord_isometry v w).continuous)
  have hcomp := hPi.comp hWA hcont
  have heq : (Pi.map (fun w : v.placesOver L => coord v w)) ∘
      algebraMap L
        ((w : v.placesOver L) →
          WithAbs (NumberField.HeightOneSpectrum.adicAbv L w.val)) =
      (fun y : L => fun w : v.placesOver L =>
        algebraMap L (w.val.adicCompletion L) y) := by
    funext y w
    simp only [Function.comp_apply, Pi.map_apply]
    have h2 := coord_comp_algebraMap v w
    have h3 : (algebraMap L
        ((w : v.placesOver L) →
          WithAbs (NumberField.HeightOneSpectrum.adicAbv L w.val))
        y) w =
        algebraMap L
          (WithAbs (NumberField.HeightOneSpectrum.adicAbv L w.val))
          y := rfl
    rw [h3]
    exact congrFun h2 y
  rwa [heq] at hcomp

theorem denseRange_completionTensorProductMap :
    DenseRange (completionTensorProductMap (K := K) (L := L) v) := by
  apply DenseRange.of_comp
    (g := fun y : L => (1 : v.adicCompletion K) ⊗ₜ[K] y)
  have heq : (completionTensorProductMap (K := K) (L := L) v) ∘
      (fun y : L => (1 : v.adicCompletion K) ⊗ₜ[K] y) =
      (fun y : L => fun w : v.placesOver L =>
        algebraMap L (w.val.adicCompletion L) y) := by
    funext y w
    simp only [Function.comp_apply]
    rw [completionTensorProductMap_tmul, map_one, one_mul]
    change algebraMap L (w.val.adicCompletion L) y = _
    rfl
  rw [heq]
  exact denseRange_algebraMap_placesOver v

theorem completionTensorProductMap_surjective :
    Function.Surjective
      (completionTensorProductMap (K := K) (L := L) v) := by
  let f :=
    (completionTensorProductMap (K := K) (L := L) v).toLinearMap
  let s : Submodule (v.adicCompletion K)
    ((w : v.placesOver L) → w.val.adicCompletion L) :=
    (⊤ : Submodule (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)).map f
  have hsRange :
      (s : Set ((w : v.placesOver L) → w.val.adicCompletion L)) = Set.range f := by
    ext y
    simp [s]
  let _ : FiniteDimensional (v.adicCompletion K) s := inferInstance
  have hsClosed : IsClosed (s : Set ((w : v.placesOver L) →
      w.val.adicCompletion L)) := by
    exact Submodule.isClosed_of_finiteDimensional
      (𝕜 := v.adicCompletion K)
      (E := ((w : v.placesOver L) → w.val.adicCompletion L)) s
  have hDense : DenseRange f :=
    denseRange_completionTensorProductMap (K := K) (L := L) v
  have hRange : Set.range f = Set.univ := by
    rw [← hsRange, ← hsClosed.closure_eq, hsRange]
    exact hDense.closure_range
  exact Set.range_eq_univ.mp hRange

end IsDedekindDomain.HeightOneSpectrum
