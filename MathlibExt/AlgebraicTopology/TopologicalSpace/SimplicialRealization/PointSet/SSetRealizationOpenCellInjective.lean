/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationColimitPresentation
public import MathlibExt.Topology.Convenient.StdSimplexMinimalFace
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.ColimitType
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# Uniqueness of nondegenerate interior realization carriers

If two nondegenerate simplex presentations with strictly positive barycentric
coordinates represent the same realization point, their nondegenerate carriers
are equal. The statement concerns carrier equality for an arbitrary simplicial
set and retains both interior hypotheses.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped Simplicial

namespace SSet

variable (X : SSet.{u})

/-- Realized tautological diagram as a private abbreviation. -/
private noncomputable abbrev diagF (X : SSet.{u}) :
    CostructuredArrow CategoryTheory.uliftYoneda X ⥤ Type u :=
  SSet.realizationColimitPresentation.realizedTautologicalDiagram X

/-- Standard-simplex point underlying a colimit element, as a new-carrier
point via `toTopHomeo`. `SSet.stdSimplex` is `uliftYoneda` by definition,
so the domain matches. -/
private noncomputable def stdPoint (X : SSet.{u})
    (y : Σ j : CostructuredArrow CategoryTheory.uliftYoneda X, (diagF X).obj j) :
    Convexity.StdSimplex ℝ (Fin (y.1.left.len + 1)) :=
  y.1.left.toTopHomeo y.2

/-- Underlying simplex of a colimit element, via `SSet.yonedaEquiv`. -/
private noncomputable def simplexOf (X : SSet.{u})
    (y : Σ j : CostructuredArrow CategoryTheory.uliftYoneda X, (diagF X).obj j) :
    X.obj (Opposite.op y.1.left) :=
  SSet.yonedaEquiv y.1.hom

/-- Point translation across a forward colimit step: the underlying standard
point maps by the coordinate function of `f.left`. -/
private lemma stdPoint_map (X : SSet.{u})
    {j j' : CostructuredArrow CategoryTheory.uliftYoneda X} (f : j ⟶ j')
    (x : (diagF X).obj j) :
    stdPoint X ⟨j', (diagF X).map f x⟩ =
      Convexity.StdSimplex.map (fun i => f.left.toOrderHom i)
        (stdPoint X ⟨j, x⟩) := by
  classical
  -- Unfold the diagram map to `SSet.toTop.map (SSet.stdSimplex.map f.left)` and
  -- Naturality of the standard-simplex realization homeomorphism.
  have h : (diagF X).map f x =
      SSet.toTop.map (SSet.stdSimplex.map f.left) x := rfl
  have hNat := SimplexCategory.toTopHomeo_naturality_apply f.left x
  have hFun : (⇑f.left : Fin (j.left.len + 1) → Fin (j'.left.len + 1)) =
      (fun i => f.left.toOrderHom i) := rfl
  rw [stdPoint, stdPoint, h, hNat, hFun]

/-- Simplex compatibility across a forward colimit step. -/
private lemma simplexOf_map (X : SSet.{u})
    {j j' : CostructuredArrow CategoryTheory.uliftYoneda X} (f : j ⟶ j')
    (x : (diagF X).obj j) :
    simplexOf X ⟨j, x⟩ = X.map f.left.op (simplexOf X ⟨j', (diagF X).map f x⟩) := by
  classical
  have hw : SSet.stdSimplex.map f.left ≫ j'.hom = j.hom := CostructuredArrow.w f
  have hnat : X.map f.left.op (SSet.yonedaEquiv j'.hom) =
      SSet.yonedaEquiv (SSet.stdSimplex.map f.left ≫ j'.hom) :=
    SSet.yonedaEquiv_naturality f.left j'.hom
  simp only [simplexOf, hnat, hw]

/-- Underlying simplex transported to `⦋left.len⦌` via `mk_len`. Casts are
explicit; dimension zero needs no special case here. -/
private noncomputable def simplexMk (X : SSet.{u})
    (y : Σ j : CostructuredArrow CategoryTheory.uliftYoneda X, (diagF X).obj j) :
    X _⦋y.1.left.len⦌ := by
  have h : (⦋y.1.left.len⦌ : SimplexCategory) = y.1.left :=
    SimplexCategory.mk_len y.1.left
  rw [h]
  exact simplexOf X y

/-- Normal-carrier witness for a colimit element: an arbitrary (not necessarily
mono) face `φ : ⦋k⦌ ⟶ y.1.left` presenting the underlying standard point by
an interior point, plus an Eilenberg-Zilber decomposition of the pulled-back
simplex. General `left` avoids `mk_len` casts; forward transport is by
composition; canonicity is recovered later via the support-face lemmas. -/
private def HasNormCarrier (X : SSet.{u})
    (y : Σ j : CostructuredArrow CategoryTheory.uliftYoneda X, (diagF X).obj j)
    (t : X.N) : Prop :=
  ∃ (k : ℕ) (φ : ⦋k⦌ ⟶ y.1.left)
    (q : Convexity.StdSimplex ℝ (Fin (k + 1))),
    (∀ i, 0 < q.weights i) ∧
    Convexity.StdSimplex.map (fun i => φ.toOrderHom i) q = stdPoint X y ∧
    ∃ (m : ℕ) (e : ⦋k⦌ ⟶ ⦋m⦌) (_ : Epi e) (tn : X.nonDegenerate m),
      X.map φ.op (simplexOf X y) = X.map e.op tn.val ∧
      t = SSet.N.mk tn.val tn.property

/-- Endpoint point computation: the underlying standard point is the given one. -/
private lemma stdPoint_sigmaPresent (X : SSet.{u}) (s : X.N)
    (p : Convexity.StdSimplex ℝ (Fin (s.dim + 1))) :
    stdPoint X ⟨SSet.realizationColimitPresentation.sigmaPresentObj X s,
      SSet.realizationColimitPresentation.sigmaPresentPoint X ⟨s, p⟩⟩ =
      p := by
  classical
  -- `sigmaPresentObj`/`sigmaPresentPoint` unfold definitionally to `mk ...` and
  -- `(toTopHomeo ⦋s.dim⦌).symm p`; `mk ... .left` is definitionally `⦋s.dim⦌`
  -- with `len` definitionally `s.dim` (same `change` pattern as the pre-migration
  -- proof, avoiding `implicit`-transparency rebuild issues).
  change ((⦋s.dim⦌.toTopHomeo) ((⦋s.dim⦌.toTopHomeo).symm p)) = p
  rw [Homeomorph.apply_symm_apply _ _]

/-- Endpoint simplex computation (point binder migrated to v4.34.1 `StdSimplex`;
the proof reasons only about the simplex, so the body is unchanged). -/
private lemma simplexMk_sigmaPresent (X : SSet.{u}) (s : X.N)
    (p : Convexity.StdSimplex ℝ (Fin (s.dim + 1))) :
    simplexMk X ⟨SSet.realizationColimitPresentation.sigmaPresentObj X s,
      SSet.realizationColimitPresentation.sigmaPresentPoint X ⟨s, p⟩⟩ =
      s.simplex := by
  classical
  have hhom : (CostructuredArrow.mk (SSet.yonedaEquiv.symm s.simplex)).hom =
      SSet.yonedaEquiv.symm s.simplex := CostructuredArrow.mk_hom_eq_self _
  change SSet.yonedaEquiv (CostructuredArrow.mk (SSet.yonedaEquiv.symm s.simplex)).hom =
    s.simplex
  rw [hhom]
  exact Equiv.apply_symm_apply _ _

/-- Base case: an interior nondegenerate presentation carries its own simplex.
Witness uses identity face and identity EZ; dimension zero is included since
`𝟙` works uniformly. Strict positivity is preserved via `weights`. -/
private lemma hasNormCarrier_sigmaPresent (X : SSet.{u}) (s : X.N)
    (p : Convexity.StdSimplex ℝ (Fin (s.dim + 1))) (hp : ∀ i, 0 < p.weights i) :
    HasNormCarrier X ⟨SSet.realizationColimitPresentation.sigmaPresentObj X s,
      SSet.realizationColimitPresentation.sigmaPresentPoint X ⟨s, p⟩⟩ s := by
  classical
  refine ⟨s.dim, 𝟙 _, p, fun i => hp i, ?_,
    s.dim, 𝟙 _, inferInstance, ⟨s.simplex, s.nonDegenerate⟩, ?_, ?_⟩
  · have hfun : (fun i => SimplexCategory.Hom.toOrderHom (𝟙 ⦋s.dim⦌) i) = id := rfl
    -- Avoid `rw [hfun]`: the face `𝟙 _` is elaborated at a type mentioning
    -- `(sigmaPresentObj X s).left`, so rebuilding the motive at `implicit`
    -- transparency fails. Rewrite by congruence instead (treats the function
    -- atomically), then close by the preflight lemmas.
    have hcongr := congrArg
      (fun g => Convexity.StdSimplex.map g p) hfun
    have hid : Convexity.StdSimplex.map id p = p := Convexity.StdSimplex.map_id p
    exact hcongr.trans (hid.trans (stdPoint_sigmaPresent X s p).symm)
  · have hhom : (CostructuredArrow.mk (SSet.yonedaEquiv.symm s.simplex)).hom =
        SSet.yonedaEquiv.symm s.simplex := CostructuredArrow.mk_hom_eq_self _
    simp only [CategoryTheory.op_id]
    congr 1
    change SSet.yonedaEquiv (CostructuredArrow.mk (SSet.yonedaEquiv.symm s.simplex)).hom =
      s.simplex
    rw [hhom]
    exact Equiv.apply_symm_apply _ _
  · cases s with
    | mk v h => rfl

/-- Epi coordinate surjectivity, explicit for dimension zero (works uniformly). -/
private lemma epi_surjective_fun {k m : ℕ} (e : ⦋k⦌ ⟶ ⦋m⦌) [Epi e] :
    Function.Surjective (fun i => e.toOrderHom i) :=
  SimplexCategory.epi_iff_surjective.mp inferInstance

/-- Epi preserves interior positivity via `map_surjective_pos` (reuse). -/
private lemma map_epi_interior {k m : ℕ} (e : ⦋k⦌ ⟶ ⦋m⦌) [Epi e]
    {q : Convexity.StdSimplex ℝ (Fin (k + 1))}
    (hq : ∀ i, 0 < q.weights i) (j : Fin (m + 1)) :
    0 < (Convexity.StdSimplex.map (fun i => e.toOrderHom i) q).weights j :=
  Convexity.StdSimplex.map_surjective_pos (epi_surjective_fun e) hq j

/-- Image normalization of a face presentation: an arbitrary face presenting `p`
by an interior point factors through its image as an epi plus a mono, the epi
transport stays interior by `map_epi_interior` (`map_surjective_pos` reuse),
and the mono face presents `p`. Dimension zero is included. -/
private lemma image_face_presents {n : ℕ}
    {p : Convexity.StdSimplex ℝ (Fin (n + 1))}
    {k : ℕ} (φ : ⦋k⦌ ⟶ ⦋n⦌) (q : Convexity.StdSimplex ℝ (Fin (k + 1)))
    (hq : ∀ i, 0 < q.weights i)
    (hmap : Convexity.StdSimplex.map (fun i => φ.toOrderHom i) q = p) :
    ∃ (r : Convexity.StdSimplex ℝ (Fin ((image φ).len + 1))),
      (∀ i, 0 < r.weights i) ∧
      Convexity.StdSimplex.map
          (fun i => (image.ι φ).toOrderHom i) r = p := by
  classical
  set e₀ := factorThruImage φ with he₀
  set ψ := image.ι φ with hψ
  have hfac : e₀ ≫ ψ = φ := image.fac φ
  refine ⟨Convexity.StdSimplex.map (fun i => e₀.toOrderHom i) q,
    fun i => map_epi_interior e₀ hq i, ?_⟩
  have hcomp : Convexity.StdSimplex.map (fun i => ψ.toOrderHom i)
        (Convexity.StdSimplex.map (fun i => e₀.toOrderHom i) q) =
      Convexity.StdSimplex.map (fun i => (e₀ ≫ ψ).toOrderHom i) q := by
    rw [← Convexity.StdSimplex.map_comp q _ _]
    rfl
  rw [hcomp, hfac]
  exact hmap

/-- Uniqueness: any two normal witnesses of the same element share the carrier.
Both faces are normalized through their images (epi + mono); epis preserve
interior by `map_epi_interior`; the mono image faces are identified by
`supportFace_eq`; the common image simplex has a unique Eilenberg-Zilber
carrier (`unique_nonDegenerate_dim/simplex`), forcing both carriers equal.
Ascriptions to `⦋·⦌` form hold by `mk_len` (rfl); dimension zero included. -/
private lemma hasNormCarrier_unique (X : SSet.{u})
    (y : Σ j : CostructuredArrow CategoryTheory.uliftYoneda X, (diagF X).obj j)
    (t₁ t₂ : X.N) :
    HasNormCarrier X y t₁ → HasNormCarrier X y t₂ → t₁ = t₂ := by
  classical
  rintro ⟨k₁, φ₁, q₁, hq₁, hmap₁, m₁, e₁, hepi₁, tn₁, heq₁, ht₁⟩
  rintro ⟨k₂, φ₂, q₂, hq₂, hmap₂, m₂, e₂, hepi₂, tn₂, heq₂, ht₂⟩
  -- Image factorizations in `⦋·⦌` form.
  set e₀₁ : ⦋k₁⦌ ⟶ ⦋(image φ₁).len⦌ :=
    factorThruImage φ₁ with he₀₁def
  set ψ₁ : ⦋(image φ₁).len⦌ ⟶ ⦋y.1.left.len⦌ :=
    image.ι φ₁ with hψ₁def
  have hfac₁ : e₀₁ ≫ ψ₁ = (φ₁ : ⦋k₁⦌ ⟶ ⦋y.1.left.len⦌) :=
    image.fac φ₁
  set e₀₂ : ⦋k₂⦌ ⟶ ⦋(image φ₂).len⦌ :=
    factorThruImage φ₂ with he₀₂def
  set ψ₂ : ⦋(image φ₂).len⦌ ⟶ ⦋y.1.left.len⦌ :=
    image.ι φ₂ with hψ₂def
  have hfac₂ : e₀₂ ≫ ψ₂ = (φ₂ : ⦋k₂⦌ ⟶ ⦋y.1.left.len⦌) :=
    image.fac φ₂
  have hmono₁ : CategoryTheory.Mono ψ₁ := by
    change CategoryTheory.Mono (image.ι _)
    infer_instance
  have hmono₂ : CategoryTheory.Mono ψ₂ := by
    change CategoryTheory.Mono (image.ι _)
    infer_instance
  -- Normalized interior presentations of the same point.
  obtain ⟨r₁, hrq₁, hpres₁⟩ :=
    image_face_presents (φ₁ : ⦋k₁⦌ ⟶ ⦋y.1.left.len⦌) q₁ hq₁ hmap₁
  obtain ⟨r₂, hrq₂, hpres₂⟩ :=
    image_face_presents (φ₂ : ⦋k₂⦌ ⟶ ⦋y.1.left.len⦌) q₂ hq₂ hmap₂
  have hpres₁' : Convexity.StdSimplex.map (fun i => ψ₁.toOrderHom i) r₁ =
      stdPoint X y := hpres₁
  have hpres₂' : Convexity.StdSimplex.map (fun i => ψ₂.toOrderHom i) r₂ =
      stdPoint X y := hpres₂
  obtain ⟨w, hψeq⟩ := Convexity.StdSimplex.supportFace_eq hmono₁ hrq₁ hpres₁' hmono₂ hrq₂ hpres₂'
  -- Preserve the epi instances before forgetting the `set` let-values: after
  -- `clear_value`, typeclass search can no longer unfold `e₀₁`/`e₀₂` to
  -- `factorThruImage`.
  have hepi₀₁ : Epi e₀₁ := inferInstance
  have hepi₀₂ : Epi e₀₂ := inferInstance
  -- Drop everything mentioning the raw `Limits.image` objects or already
  -- consumed by `supportFace_eq`: the `set` equations/let-values (their types
  -- mention `image φ`) and the normalized presentations `r` (their statements
  -- mention `image.ι φ`). All block dependent elimination of `w` (unifier
  -- chases `(image φ₂).1 = (image φ₁).1`); none is used below.
  clear_value e₀₁ ψ₁ e₀₂ ψ₂
  clear he₀₁def hψ₁def he₀₂def hψ₂def r₁ hrq₁ hpres₁ r₂ hrq₂ hpres₂ hpres₁' hpres₂'
  -- Generalize the image dimensions to opaque variables *before* eliminating
  -- `w`: with variable sides, `subst` never has to unify the raw
  -- `Limits.image` objects (which `cases` chases as
  -- `(image φ₂).1 = (image φ₁).1`). No revert/intro round-trip is needed.
  generalize hl₁ : (image φ₁).len = l₁ at *
  generalize hl₂ : (image φ₂).len = l₂ at *
  cases w
  clear hl₁ hl₂
  -- `apply` (not `ext`) controls the depth: `Hom.ext` reduces to an
  -- `OrderHom` equality, `DFunLike.ext` to pointwise `⇑`-equality. A bare
  -- `ext i` over-applies down to `Fin.val`, which `hψeq` does not have.
  have hmor : ψ₁ = ψ₂ := by
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    simpa using hψeq i
  -- Common image simplex and its EZ decomposition.
  set a := simplexOf X y with hadef
  set b := X.map ψ₁.op a with hbdef
  have hb₂eq : X.map ψ₂.op a = b := by rw [← hmor]
  obtain ⟨mb, eb, hepi_b, tb, hb_ez⟩ := X.exists_nonDegenerate b
  have := epi_comp e₀₁ eb
  have := epi_comp e₀₂ eb
  -- Side 1 reduces through the common simplex.
  have hpull₁ : X.map φ₁.op a = X.map e₀₁.op b := by
    have h := congrArg (fun g => X.map g.op a) hfac₁
    simpa [Functor.map_comp] using h.symm
  have hred₁ : X.map φ₁.op a = X.map (e₀₁ ≫ eb).op tb.val := by
    rw [hpull₁, hb_ez]
    simp [Functor.map_comp]
  have hdim₁ : mb = m₁ := X.unique_nonDegenerate_dim _ _ tb hred₁ _ tn₁ heq₁
  subst hdim₁
  have htb₁ : tb = tn₁ := X.unique_nonDegenerate_simplex _ _ tb hred₁ _ tn₁ heq₁
  -- Side 2 reduces through the same simplex.
  have hpull₂ : X.map φ₂.op a = X.map e₀₂.op (X.map ψ₂.op a) := by
    have h := congrArg (fun g => X.map g.op a) hfac₂
    simpa [Functor.map_comp] using h.symm
  have hred₂ : X.map φ₂.op a = X.map (e₀₂ ≫ eb).op tb.val := by
    rw [hpull₂, hb₂eq, hb_ez]
    simp [Functor.map_comp]
  have hdim₂ : mb = m₂ := X.unique_nonDegenerate_dim _ _ tb hred₂ _ tn₂ heq₂
  subst hdim₂
  have htb₂ : tb = tn₂ := X.unique_nonDegenerate_simplex _ _ tb hred₂ _ tn₂ heq₂
  rw [ht₁, ht₂, ← htb₁, ← htb₂]

/-- Canonical existence: every element has a normal witness, via the support
face (`exists_support_face_mono` reuse) and Eilenberg-Zilber decomposition.
The support mono is used as an arbitrary face; dimension zero is included
since support cardinality is positive. -/
private lemma hasNormCarrier_exists (X : SSet.{u})
    (y : Σ j : CostructuredArrow CategoryTheory.uliftYoneda X, (diagF X).obj j) :
    ∃ t, HasNormCarrier X y t := by
  classical
  obtain ⟨k, φ, _hmono, q, hq, hmap⟩ :=
    Convexity.StdSimplex.exists_support_face_mono (stdPoint X y)
  set a₁ : X _⦋k⦌ := X.map φ.op (simplexOf X y) with ha₁def
  obtain ⟨m, e, hepi, tn, hez⟩ := X.exists_nonDegenerate a₁
  exact ⟨SSet.N.mk tn.val tn.property, k, φ, q, hq, hmap, m, e, hepi, tn, hez, rfl⟩

/-- Forward preservation: a directed colimit step carries every normal witness
forward by composing the face. Point transport uses `stdPoint_map` with
`map_comp`; simplex transport uses `simplexOf_map` with functoriality.
Explicit variance: `φ' = f.left ≫ φ` reversed to `φ.op ≫ f.left.op` under `op`.
Dimension zero needs no special case. -/
private lemma hasNormCarrier_forward (X : SSet.{u})
    {j j' : CostructuredArrow CategoryTheory.uliftYoneda X}
    {x : (diagF X).obj j} {x' : (diagF X).obj j'}
    (f : j ⟶ j') (hf : x' = (diagF X).map f x) (t : X.N) :
    HasNormCarrier X ⟨j, x⟩ t → HasNormCarrier X ⟨j', x'⟩ t := by
  classical
  rintro ⟨k, φ, q, hq, hmap, m, e, hepi, tn, heq, ht⟩
  refine ⟨k, φ ≫ f.left, q, hq, ?_, m, e, hepi, tn, ?_, ht⟩
  · have hcomp : Convexity.StdSimplex.map (fun i => (φ ≫ f.left).toOrderHom i) q =
        Convexity.StdSimplex.map (fun i => f.left.toOrderHom i)
          (Convexity.StdSimplex.map (fun i => φ.toOrderHom i) q) := by
      rw [← Convexity.StdSimplex.map_comp q _ _]
      rfl
    rw [hcomp, hmap]
    have hpt : stdPoint X ⟨j', x'⟩ =
        Convexity.StdSimplex.map (fun i => f.left.toOrderHom i)
          (stdPoint X ⟨j, x⟩) := by
      rw [hf]
      exact stdPoint_map X f x
    exact hpt.symm
  · have hsim : simplexOf X ⟨j, x⟩ =
        X.map f.left.op (simplexOf X ⟨j', x'⟩) := by
      rw [hf]
      exact simplexOf_map X f x
    have hfun : X.map (φ ≫ f.left).op (simplexOf X ⟨j', x'⟩) =
        X.map φ.op (X.map f.left.op (simplexOf X ⟨j', x'⟩)) := by
      simp [Functor.map_comp]
    rw [hfun, ← hsim]
    exact heq

/-- Backward preservation: a directed colimit step reflects every normal
witness. From the canonical witness of the source, forward preservation gives
the canonical carrier at the target; uniqueness identifies it with the given
carrier. Explicit variance is handled in the forward step; dimension zero is
included. -/
private lemma hasNormCarrier_backward (X : SSet.{u})
    {j j' : CostructuredArrow CategoryTheory.uliftYoneda X}
    {x : (diagF X).obj j} {x' : (diagF X).obj j'}
    (f : j ⟶ j') (hf : x' = (diagF X).map f x) (t : X.N) :
    HasNormCarrier X ⟨j', x'⟩ t → HasNormCarrier X ⟨j, x⟩ t := by
  classical
  intro h'
  obtain ⟨t_c, hc⟩ := hasNormCarrier_exists X ⟨j, x⟩
  have hfwd := hasNormCarrier_forward X f hf t_c hc
  have heq := hasNormCarrier_unique X ⟨j', x'⟩ t_c t hfwd h'
  rw [heq] at hc
  exact hc

/-- Normal carriers are constant along the generated colimit relation: the
relation case is forward plus backward preservation; the other cases are the
`Iff` combinators. Arbitrary intermediate representatives are handled since
every witness and every step is general. -/
private lemma hasNormCarrier_eqvGen (X : SSet.{u}) (t : X.N)
    (x y : Σ j : CostructuredArrow CategoryTheory.uliftYoneda X, (diagF X).obj j)
    (h : Relation.EqvGen (diagF X).ColimitTypeRel x y) :
    HasNormCarrier X x t ↔ HasNormCarrier X y t := by
  classical
  induction h with
  | rel x y hrel =>
    obtain ⟨f, hf⟩ := hrel
    obtain ⟨j, xv⟩ := x
    obtain ⟨j', xv'⟩ := y
    constructor
    · intro hx
      exact hasNormCarrier_forward X f hf _ hx
    · intro hy
      exact hasNormCarrier_backward X f hf _ hy
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz

/--
For any simplicial set, two nondegenerate simplex presentations of the same
realization point have equal carriers when all barycentric coordinates in both
presentations are strictly positive.
-/
public theorem carrier_eq_of_sigmaToTop_eq_of_interior (X : SSet.{u})
    (s₁ s₂ : X.N)
    (p₁ : Convexity.StdSimplex ℝ (Fin (s₁.dim + 1)))
    (p₂ : Convexity.StdSimplex ℝ (Fin (s₂.dim + 1)))
    (h₁ : ∀ i, 0 < p₁.weights i) (h₂ : ∀ i, 0 < p₂.weights i)
    (h : SSet.sigmaToTop X ⟨s₁, p₁⟩ = SSet.sigmaToTop X ⟨s₂, p₂⟩) :
    s₁ = s₂ := by
  classical
  have heqv := SSet.realizationColimitPresentation.sigmaToTop_eq_to_eqvGen_colimitTypeRel
    X ⟨s₁, p₁⟩ ⟨s₂, p₂⟩ h
  have hbase₁ := hasNormCarrier_sigmaPresent X s₁ p₁ h₁
  have htrans := (hasNormCarrier_eqvGen X s₁ _ _ heqv).mp hbase₁
  have hbase₂ := hasNormCarrier_sigmaPresent X s₂ p₂ h₂
  exact hasNormCarrier_unique X _ s₁ s₂ htrans hbase₂

end SSet
