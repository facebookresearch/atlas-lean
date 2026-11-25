/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Excision.PositiveBarFiltration
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Positive coefficient-bar graded quotients

Ideal-count stages in the positive coefficient
bar form subcomplexes with zero augmentation
term. The kernel boundary restricts and
descends to the word-layer quotients.
Arbitrary coefficient universes are retained.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (I : NonUnitalSubalgebra k A) [I.IsTwoSided]
  (V : Type w) [AddCommGroup V] [Module k V]

/-- The original positive count family, with its bottom degree. -/
def barFullWordFiltration (p : ℕ) :
    ∀ n : ℕ, Submodule k ((relativePositiveBarComplex k A I V).X n)
  | 0 => ⊥
  | n + 1 => barWordFiltration k A I V p n

/-- The original lower count stage, with bottom at filtration index zero. -/
def barFullLowerWordFiltration (p n : ℕ) :
    Submodule k ((relativePositiveBarComplex k A I V).X n) :=
  if p = 0 then ⊥ else barFullWordFiltration k A I V (p - 1) n

@[simp]
theorem barFullWordFiltration_succ (p n : ℕ) :
    barFullWordFiltration k A I V p (n + 1) = barWordFiltration k A I V p n := rfl

@[simp]
theorem barFullLowerWordFiltration_succ (p n : ℕ) :
    barFullLowerWordFiltration k A I V p (n + 1) =
      barLowerFiltration k A I V p n := rfl

theorem barFullWordFiltration_mono {p q : ℕ} (h : p ≤ q) (n : ℕ) :
    barFullWordFiltration k A I V p n ≤ barFullWordFiltration k A I V q n := by
  cases n with
  | zero => exact le_refl _
  | succ n => exact barWordFiltration_mono k A I V h n

/-- The degree-one boundary lands in the zero augmentation; other degrees use accepted b′. -/
theorem barFullWordFiltration_d (p n : ℕ) :
    (barFullWordFiltration k A I V p (n + 1)).map
        ((relativePositiveBarComplex k A I V).d (n + 1) n).hom ≤
      barFullWordFiltration k A I V p n := by
  cases n with
  | zero =>
      rw [Submodule.map_le_iff_le_comap]
      intro x _hx
      change ((relativePositiveBarComplex k A I V).d 1 0).hom x = 0
      have hd : (relativePositiveBarComplex k A I V).d 1 0 = 0 :=
        (relativePositiveBarComplex_isZero_zero k A I V).eq_of_tgt _ _
      rw [hd]
      rfl
  | succ n =>
      exact barWordFiltration_d k A I V p n

theorem barFullLowerWordFiltration_le (p n : ℕ) :
    barFullLowerWordFiltration k A I V p n ≤ barFullWordFiltration k A I V p n := by
  by_cases hp : p = 0
  · simp only [barFullLowerWordFiltration, hp, ite_eq_left, bot_le]
  · simpa only [barFullLowerWordFiltration, ite_eq_right hp] using
      (barFullWordFiltration_mono k A I V (Nat.sub_le p 1) n)

theorem barFullLowerWordFiltration_d (p n : ℕ) :
    (barFullLowerWordFiltration k A I V p (n + 1)).map
        ((relativePositiveBarComplex k A I V).d (n + 1) n).hom ≤
      barFullLowerWordFiltration k A I V p n := by
  by_cases hp : p = 0
  · subst p
    simp [barFullLowerWordFiltration]
  · simpa only [barFullLowerWordFiltration, ite_eq_right hp] using
      (barFullWordFiltration_d k A I V (p - 1) n)

private theorem originalPositiveBarBoundary_square (n : ℕ)
    (x : (relativePositiveBarComplex k A I V).X (n + 2)) :
    ((relativePositiveBarComplex k A I V).d (n + 1) n).hom
      (((relativePositiveBarComplex k A I V).d (n + 2) (n + 1)).hom x) = 0 := by
  have h := congrArg
    (fun f : (relativePositiveBarComplex k A I V).X (n + 2) ⟶
      (relativePositiveBarComplex k A I V).X n => f.hom x)
    ((relativePositiveBarComplex k A I V).d_comp_d (n + 2) (n + 1) n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_zero, LinearMap.zero_apply] using h

/-- The positive-kernel boundary restricted to the full original count stages. -/
def barStageD (p n : ℕ) :
    barFullWordFiltration k A I V p (n + 1) →ₗ[k] barFullWordFiltration k A I V p n :=
  LinearMap.codRestrict (barFullWordFiltration k A I V p n)
    (((relativePositiveBarComplex k A I V).d (n + 1) n).hom.domRestrict
      (barFullWordFiltration k A I V p (n + 1)))
    (fun x => (Submodule.map_le_iff_le_comap.mp
      (barFullWordFiltration_d k A I V p n)) x.property)

/-- The positive-kernel boundary restricted to the original lower stages. -/
def barLowerStageD (p n : ℕ) :
    barFullLowerWordFiltration k A I V p (n + 1) →ₗ[k]
      barFullLowerWordFiltration k A I V p n :=
  LinearMap.codRestrict (barFullLowerWordFiltration k A I V p n)
    (((relativePositiveBarComplex k A I V).d (n + 1) n).hom.domRestrict
      (barFullLowerWordFiltration k A I V p (n + 1)))
    (fun x => (Submodule.map_le_iff_le_comap.mp
      (barFullLowerWordFiltration_d k A I V p n)) x.property)

private theorem barStageD_square (p n : ℕ) :
    ModuleCat.ofHom (barStageD k A I V p (n + 1)) ≫
      ModuleCat.ofHom (barStageD k A I V p n) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change ((relativePositiveBarComplex k A I V).d (n + 1) n).hom
      (((relativePositiveBarComplex k A I V).d (n + 2) (n + 1)).hom x.val) = 0
  exact originalPositiveBarBoundary_square k A I V n x.val

private theorem barLowerStageD_square (p n : ℕ) :
    ModuleCat.ofHom (barLowerStageD k A I V p (n + 1)) ≫
      ModuleCat.ofHom (barLowerStageD k A I V p n) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change ((relativePositiveBarComplex k A I V).d (n + 1) n).hom
      (((relativePositiveBarComplex k A I V).d (n + 2) (n + 1)).hom x.val) = 0
  exact originalPositiveBarBoundary_square k A I V n x.val

/-- The original positive Fp family is a chain subcomplex. -/
def barFilteredWordComplex (p : ℕ) : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of k (barFullWordFiltration k A I V p n))
    (fun n => ModuleCat.ofHom (barStageD k A I V p n)) (by exact barStageD_square k A I V p)

/-- Its lower family is bottom at p=0 and the original previous stage otherwise. -/
def barLowerWordComplex (p : ℕ) : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of k (barFullLowerWordFiltration k A I V p n))
    (fun n => ModuleCat.ofHom (barLowerStageD k A I V p n))
    (by exact barLowerStageD_square k A I V p)

@[simp]
theorem barFilteredWordComplex_X_succ (p n : ℕ) :
    (barFilteredWordComplex k A I V p).X (n + 1) =
      ModuleCat.of k (barWordFiltration k A I V p n) := rfl

private theorem barFilteredWordComplex_d (p n : ℕ) :
    (barFilteredWordComplex k A I V p).d (n + 1) n =
      ModuleCat.ofHom (barStageD k A I V p n) :=
  ChainComplex.of_d (fun m => ModuleCat.of k (barFullWordFiltration k A I V p m))
    (fun m => ModuleCat.ofHom (barStageD k A I V p m)) n

private theorem barLowerWordComplex_d (p n : ℕ) :
    (barLowerWordComplex k A I V p).d (n + 1) n =
      ModuleCat.ofHom (barLowerStageD k A I V p n) :=
  ChainComplex.of_d (fun m => ModuleCat.of k (barFullLowerWordFiltration k A I V p m))
    (fun m => ModuleCat.ofHom (barLowerStageD k A I V p m)) n

/-- The original positive-stage vector retains its original kernel boundary value. -/
theorem barFilteredWordComplex_d_val (p n : ℕ)
    (x : barFullWordFiltration k A I V p (n + 1)) :
    (barFullWordFiltration k A I V p n).subtype
      (((barFilteredWordComplex k A I V p).d (n + 1) n).hom x) =
      ((relativePositiveBarComplex k A I V).d (n + 1) n).hom x.val := by
  rw [barFilteredWordComplex_d]
  rfl

/-- The original subtype family is the inclusion into the original positive kernel. -/
def barFilteredWordInclusion (p : ℕ) :
    barFilteredWordComplex k A I V p ⟶ relativePositiveBarComplex k A I V :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (barFullWordFiltration k A I V p n).subtype)
    (fun n => by
      rw [barFilteredWordComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl)

@[simp]
theorem barFilteredWordInclusion_f_succ (p n : ℕ) :
    (barFilteredWordInclusion k A I V p).f (n + 1) =
      ModuleCat.ofHom (barWordFiltration k A I V p n).subtype := rfl

/-- The lower filtration submodule includes into the current stage. -/
def barLowerWordInclusion (p : ℕ) :
    barLowerWordComplex k A I V p ⟶ barFilteredWordComplex k A I V p :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom
    (Submodule.inclusion (barFullLowerWordFiltration_le k A I V p n)))
    (fun n => by
      rw [barFilteredWordComplex_d, barLowerWordComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rfl)

/-- The original increasing stage inclusions commute with the native restricted differential. -/
def barFilteredWordMap {p q : ℕ} (h : p ≤ q) :
    barFilteredWordComplex k A I V p ⟶ barFilteredWordComplex k A I V q :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom
    (Submodule.inclusion (barFullWordFiltration_mono k A I V h n)))
    (fun n => by
      rw [barFilteredWordComplex_d, barFilteredWordComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rfl)

/-- The original positive layer quotients, extended by their bottom augmentation quotient. -/
abbrev barFullWordLayer (p n : ℕ) :=
  barFullWordFiltration k A I V p n ⧸
    (barFullLowerWordFiltration k A I V p n).comap
      (barFullWordFiltration k A I V p n).subtype

/-- The native quotient projection of the original full count stage. -/
def barFullWordLayerProjection (p n : ℕ) :
    barFullWordFiltration k A I V p n →ₗ[k] barFullWordLayer k A I V p n :=
  ((barFullLowerWordFiltration k A I V p n).comap
    (barFullWordFiltration k A I V p n).subtype).mkQ

/-- The original positive-kernel boundary descended to the full layer quotients. -/
def barLayerD (p n : ℕ) :
    barFullWordLayer k A I V p (n + 1) →ₗ[k] barFullWordLayer k A I V p n :=
  ((barFullLowerWordFiltration k A I V p (n + 1)).comap
    (barFullWordFiltration k A I V p (n + 1)).subtype).mapQ
    ((barFullLowerWordFiltration k A I V p n).comap
      (barFullWordFiltration k A I V p n).subtype)
    (barStageD k A I V p n) (by
      intro x hx
      change ((relativePositiveBarComplex k A I V).d (n + 1) n).hom x.val ∈
        barFullLowerWordFiltration k A I V p n
      exact (Submodule.map_le_iff_le_comap.mp
        (barFullLowerWordFiltration_d k A I V p n)) hx)

private theorem barLayerD_projection (p n : ℕ)
    (x : barFullWordFiltration k A I V p (n + 1)) :
    barLayerD k A I V p n (barFullWordLayerProjection k A I V p (n + 1) x) =
      barFullWordLayerProjection k A I V p n (barStageD k A I V p n x) := rfl

private theorem barLayerD_square (p n : ℕ) :
    ModuleCat.ofHom (barLayerD k A I V p (n + 1)) ≫
      ModuleCat.ofHom (barLayerD k A I V p n) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  refine Submodule.Quotient.induction_on _ y ?_
  intro x
  change barLayerD k A I V p n
    (barLayerD k A I V p (n + 1) (barFullWordLayerProjection k A I V p (n + 2) x)) = 0
  rw [barLayerD_projection, barLayerD_projection]
  have hs : barStageD k A I V p n (barStageD k A I V p (n + 1) x) = 0 := by
    apply Subtype.ext
    exact originalPositiveBarBoundary_square k A I V n x.val
  rw [hs, map_zero]

/-- Its positive terms are exactly the original barWordLayer quotients. -/
def barAssociatedWordComplex (p : ℕ) : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of k (barFullWordLayer k A I V p n))
    (fun n => ModuleCat.ofHom (barLayerD k A I V p n)) (by exact barLayerD_square k A I V p)

@[simp]
theorem barAssociatedWordComplex_X_succ (p n : ℕ) :
    (barAssociatedWordComplex k A I V p).X (n + 1) =
      ModuleCat.of k (barWordLayer k A I V p n) := rfl

private theorem barAssociatedWordComplex_d (p n : ℕ) :
    (barAssociatedWordComplex k A I V p).d (n + 1) n =
      ModuleCat.ofHom (barLayerD k A I V p n) :=
  ChainComplex.of_d (fun m => ModuleCat.of k (barFullWordLayer k A I V p m))
    (fun m => ModuleCat.ofHom (barLayerD k A I V p m)) n

/-- The native original quotient projections commute with the original restricted b′ maps. -/
def barAssociatedWordProjection (p : ℕ) :
    barFilteredWordComplex k A I V p ⟶ barAssociatedWordComplex k A I V p :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (barFullWordLayerProjection k A I V p n))
    (fun n => by
      rw [barFilteredWordComplex_d, barAssociatedWordComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact barLayerD_projection k A I V p n x)

/-- On positive terms the associated differential uses the original layer projection. -/
theorem barAssociatedWordComplex_d_projection (p n : ℕ)
    (x : barWordFiltration k A I V p (n + 1)) :
    ((barAssociatedWordComplex k A I V p).d (n + 2) (n + 1)).hom
        (barWordLayerProjection k A I V p (n + 1) x) =
      barWordLayerProjection k A I V p n
        (((barFilteredWordComplex k A I V p).d (n + 2) (n + 1)).hom x) := by
  rw [barAssociatedWordComplex_d, barFilteredWordComplex_d]
  exact barLayerD_projection k A I V p (n + 1) x

@[simp]
theorem barAssociatedWordProjection_f_succ (p n : ℕ) :
    (barAssociatedWordProjection k A I V p).f (n + 1) =
      ModuleCat.ofHom (barWordLayerProjection k A I V p n) := rfl

theorem barLowerWordInclusion_projection (p : ℕ) :
    barLowerWordInclusion k A I V p ≫ barAssociatedWordProjection k A I V p = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change barFullWordLayerProjection k A I V p n
    (Submodule.inclusion (barFullLowerWordFiltration_le k A I V p n) x) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact x.property

/-- The native quotient augmentation is actually zero, not a supplied acyclicity premise. -/
theorem barAssociatedWordComplex_isZero_zero (p : ℕ) :
    IsZero ((barAssociatedWordComplex k A I V p).X 0) := by
  change IsZero (ModuleCat.of k (barFullWordLayer k A I V p 0))
  apply (IsZero.iff_id_eq_zero _).mpr
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  refine Submodule.Quotient.induction_on _ y ?_
  intro x
  have hx : x = 0 := by
    apply Subtype.ext
    simpa only [barFullWordFiltration, Submodule.mem_bot, ZeroMemClass.coe_zero] using
      x.property
  change Submodule.Quotient.mk x = (0 : barFullWordLayer k A I V p 0)
  rw [hx]
  rfl

@[simp]
theorem barLowerWordComplex_zero_X (n : ℕ) :
    (barLowerWordComplex k A I V 0).X n =
      ModuleCat.of k (⊥ : Submodule k ((relativePositiveBarComplex k A I V).X n)) := rfl

end ModuleCat.Algebra.Hochschild.NonUnital
