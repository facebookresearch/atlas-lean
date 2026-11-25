/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialResolution
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

/-!
# Actual canonical polynomial generator points and their epi images

In degree n, a generator is indexed by the actual k-algebra T^n A, rather
than an arbitrary variable type. Evaluation by the actual polynomial counit
retracts its variable inclusion. Thus the generator-point map is injective
without Nontrivial k; when k is zero its actual algebra index is singleton.

The canonical algebra degeneracies preserve generator points. A positive
face splits each elementary degeneracy and preserves generator points, so
every degeneracy preimage of a generator is again a generator. Native epi
factorization earns image and preimage closure for every original epi.

The whole underlying simplicial set retains the original evaluation first
face. No simplicial-set structure is imposed on the generator indices.
These facts permit restricting its native Eilenberg--Zilber decomposition
to generator points. No contraction or splitting certificate is input.
Source proposals only; UNEXECUTED.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v

namespace CommAlgCat.CanonicalPolynomialGeneratorPoints

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

abbrev resolution : SimplicialObject (CommAlgCat.{max u v} k) :=
  (polynomialResolution.{u, v} k A).left

/-- The actual index is a native algebra carrier, not an arbitrary σ. -/
abbrev Index (n : ℕ) : Type (max u v) := (polynomialPower.{u, v} k n).obj A

/-- The entire underlying simplicial set, including its evaluation first face. -/
abbrev underlying : SSet.{max u v} :=
  resolution k A ⋙ forget (CommAlgCat.{max u v} k)

/-- The canonical generator point in the original degree object. -/
def point (n : ℕ) (x : Index k A n) : (resolution k A).obj (op ⦋n⦌) :=
  polynomialResolutionGenerator.{u, v} k A n x

/-- Actual polynomial evaluation into the preceding native algebra. -/
def indexHom (n : ℕ) : (resolution k A).obj (op ⦋n⦌) ⟶
    (polynomialPower.{u, v} k n).obj A :=
  (polynomialResolutionObjIso.{u, v} k A n).hom ≫
    (polynomialComonad.{u, v} k).ε.app ((polynomialPower.{u, v} k n).obj A)

/-- The original counit retracts the generator point in every degree. -/
@[simp]
theorem indexHom_point (n : ℕ) (x : Index k A n) :
    (indexHom k A n).hom (point k A n x) = x := by
  change ((polynomialComonad.{u, v} k).ε.app ((polynomialPower.{u, v} k n).obj A)).hom
    ((polynomialResolutionObjIso.{u, v} k A n).hom.hom
      (polynomialResolutionGenerator.{u, v} k A n x)) = x
  rw [polynomialResolutionObjIso_hom_generator, polynomialComonad_counit_X]

/-- This is a fully typed retract on actual bar algebra indices. -/
theorem indexHom_leftInverse (n : ℕ) :
    Function.LeftInverse (indexHom k A n).hom (point k A n) :=
  indexHom_point k A n

/-- No nontrivial-ground-ring hypothesis is needed for the actual indices. -/
theorem point_injective (n : ℕ) : Function.Injective (point k A n) :=
  (indexHom_leftInverse k A n).injective

/-- Polynomial generator form in the original algebra degree. -/
def IsGenerator (n : ℕ) (y : (resolution k A).obj (op ⦋n⦌)) : Prop :=
  ∃ x : Index k A n, y = point k A n x

theorem point_isGenerator (n : ℕ) (x : Index k A n) : IsGenerator k A n (point k A n x) :=
  ⟨x, rfl⟩

theorem point_indexHom {n : ℕ} {y : (resolution k A).obj (op ⦋n⦌)}
    (hy : IsGenerator k A n y) : point k A n ((indexHom k A n).hom y) = y := by
  rcases hy with ⟨x, rfl⟩
  rw [indexHom_point]

/-- Every positive original algebra face preserves polynomial generator form. -/
theorem positive_face_point {n : ℕ} (i : Fin (n + 1)) (x : Index k A (n + 1)) :
    ((resolution k A).δ i.succ).hom (point k A (n + 1) x) =
      point k A n ((Comonad.cobarEpsilonAtPos (polynomialComonad.{u, v} k) n i A).hom x) :=
  polynomialResolution_face_succ_generator.{u, v} k A i x

theorem degeneracy_point_isGenerator (n : ℕ) (i : Fin (n + 1)) (x : Index k A n) :
    IsGenerator k A (n + 1) (((resolution k A).σ i).hom (point k A n x)) := by
  cases n with
  | zero =>
    have hi : i = 0 := Fin.ext (by have h := i.isLt; simp only [Nat.zero_add] at h; omega)
    subst i
    exact ⟨point k A 0 x, polynomialResolution_degeneracy_zero_generator.{u, v} k A 0 x⟩
  | succ n =>
    cases i using Fin.cases with
    | zero =>
      exact ⟨point k A (n + 1) x,
        polynomialResolution_degeneracy_zero_generator.{u, v} k A (n + 1) x⟩
    | succ i =>
      exact ⟨(Comonad.cobarDeltaAtPos (polynomialComonad.{u, v} k) (n + 1) i A).hom x,
        polynomialResolution_degeneracy_succ_generator.{u, v} k A i x⟩

theorem degeneracy_image_generator {n : ℕ} (i : Fin (n + 1))
    (y : (resolution k A).obj (op ⦋n⦌)) (hy : IsGenerator k A n y) :
    IsGenerator k A (n + 1) (((resolution k A).σ i).hom y) := by
  rcases hy with ⟨x, rfl⟩
  exact degeneracy_point_isGenerator k A n i x

/-- The positive face δ_(i+1), rather than an assumed generator-index face,
recovers the original polynomial generator from an elementary degeneracy. -/
theorem degeneracy_preimage_generator {n : ℕ} (i : Fin (n + 1))
    (y : (resolution k A).obj (op ⦋n⦌))
    (hy : IsGenerator k A (n + 1) (((resolution k A).σ i).hom y)) :
    IsGenerator k A n y := by
  rcases hy with ⟨x, hx⟩
  have hsplit := AlgHom.congr_fun (congrArg CommAlgCat.Hom.hom
    ((resolution k A).δ_comp_σ_succ (i := i))) y
  change ((resolution k A).δ i.succ).hom (((resolution k A).σ i).hom y) = y at hsplit
  refine ⟨(Comonad.cobarEpsilonAtPos (polynomialComonad.{u, v} k) n i A).hom x, ?_⟩
  calc
    y = ((resolution k A).δ i.succ).hom (((resolution k A).σ i).hom y) := hsplit.symm
    _ = ((resolution k A).δ i.succ).hom (point k A (n + 1) x) := congrArg _ hx
    _ = point k A n _ := positive_face_point k A i x

/-- Every original epi sends generator points to generator points. -/
theorem epi_image_generator {n m : ℕ} (e : ⦋n⦌ ⟶ ⦋m⦌) [Epi e]
    (y : (resolution k A).obj (op ⦋m⦌)) (hy : IsGenerator k A m y) :
    IsGenerator k A n (((resolution k A).map e.op).hom y) := by
  induction n generalizing m with
  | zero =>
    have hm : m = 0 := by
      have h := SimplexCategory.len_le_of_epi e
      change m ≤ 0 at h
      omega
    subst m
    have he : e = 𝟙 ⦋0⦌ := SimplexCategory.eq_id_of_epi e
    subst e
    have hmap : (((resolution k A).map (𝟙 (op ⦋0⦌))).hom y) = y := by
      exact (congrArg (fun f => f.hom y) ((resolution k A).map_id (op ⦋0⦌))).trans rfl
    simpa only [op_id, hmap] using hy
  | succ n ih =>
    by_cases hm : m = n + 1
    · subst m
      have he : e = 𝟙 ⦋n + 1⦌ := SimplexCategory.eq_id_of_epi e
      subst e
      have hmap : (((resolution k A).map (𝟙 (op ⦋n + 1⦌))).hom y) = y := by
        exact (congrArg (fun f => f.hom y) ((resolution k A).map_id (op ⦋n + 1⦌))).trans rfl
      simpa only [op_id, hmap] using hy
    · have hnot : ¬ Function.Injective e.toOrderHom := by
        intro hinj
        letI : Mono e := SimplexCategory.mono_iff_injective.mpr hinj
        have h₁ := SimplexCategory.len_le_of_epi e
        have h₂ := SimplexCategory.len_le_of_mono e
        change m ≤ n + 1 at h₁
        change n + 1 ≤ m at h₂
        omega
      obtain ⟨i, e', he⟩ := SimplexCategory.eq_σ_comp_of_not_injective e hnot
      letI : Epi e' := by
        letI : Epi (SimplexCategory.σ i ≫ e') := by rw [← he]; infer_instance
        exact CategoryTheory.epi_of_epi (SimplexCategory.σ i) e'
      have hfac : ((resolution k A).map e.op).hom y =
          ((resolution k A).σ i).hom (((resolution k A).map e'.op).hom y) := by
        rw [he, op_comp, (resolution k A).map_comp]
        rfl
      rw [hfac]
      exact degeneracy_image_generator k A i _ (ih e' y hy)

/-- Every original epi preimage of a generator has polynomial generator form. -/
theorem epi_preimage_generator {n m : ℕ} (e : ⦋n⦌ ⟶ ⦋m⦌) [Epi e]
    (y : (resolution k A).obj (op ⦋m⦌))
    (hy : IsGenerator k A n (((resolution k A).map e.op).hom y)) : IsGenerator k A m y := by
  induction n generalizing m with
  | zero =>
    have hm : m = 0 := by
      have h := SimplexCategory.len_le_of_epi e
      change m ≤ 0 at h
      omega
    subst m
    have he : e = 𝟙 ⦋0⦌ := SimplexCategory.eq_id_of_epi e
    subst e
    have hmap : (((resolution k A).map (𝟙 (op ⦋0⦌))).hom y) = y := by
      exact (congrArg (fun f => f.hom y) ((resolution k A).map_id (op ⦋0⦌))).trans rfl
    simpa only [op_id, hmap] using hy
  | succ n ih =>
    by_cases hm : m = n + 1
    · subst m
      have he : e = 𝟙 ⦋n + 1⦌ := SimplexCategory.eq_id_of_epi e
      subst e
      have hmap : (((resolution k A).map (𝟙 (op ⦋n + 1⦌))).hom y) = y := by
        exact (congrArg (fun f => f.hom y) ((resolution k A).map_id (op ⦋n + 1⦌))).trans rfl
      simpa only [op_id, hmap] using hy
    · have hnot : ¬ Function.Injective e.toOrderHom := by
        intro hinj
        letI : Mono e := SimplexCategory.mono_iff_injective.mpr hinj
        have h₁ := SimplexCategory.len_le_of_epi e
        have h₂ := SimplexCategory.len_le_of_mono e
        change m ≤ n + 1 at h₁
        change n + 1 ≤ m at h₂
        omega
      obtain ⟨i, e', he⟩ := SimplexCategory.eq_σ_comp_of_not_injective e hnot
      letI : Epi e' := by
        letI : Epi (SimplexCategory.σ i ≫ e') := by rw [← he]; infer_instance
        exact CategoryTheory.epi_of_epi (SimplexCategory.σ i) e'
      have hfac : ((resolution k A).map e.op).hom y =
          ((resolution k A).σ i).hom (((resolution k A).map e'.op).hom y) := by
        rw [he, op_comp, (resolution k A).map_comp]
        rfl
      rw [hfac] at hy
      exact ih e' y (degeneracy_preimage_generator k A i _ hy)

/-- Actual nondegenerate generator INDICES are selected by their points in
the entire original underlying simplicial set. -/
abbrev Variables (n : ℕ) : Type (max u v) :=
  {x : Index k A n // point k A n x ∈ (underlying k A).nonDegenerate n}

end CommAlgCat.CanonicalPolynomialGeneratorPoints

end
