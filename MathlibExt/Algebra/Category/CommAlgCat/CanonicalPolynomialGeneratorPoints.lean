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
# Generator points in the polynomial-comonad resolution

Let `k : Type u` be a commutative ring and `A : CommAlgCat.{max u v} k`. In degree `n`, the
polynomial resolution has object `T^{n+1}A`, with generator index type the carrier of `T^n A`.
The generator-point inclusion is retracted by outer polynomial evaluation, so it is injective.

Positive faces and simplex epimorphisms preserve generator points; an epimorphism preimage of
a generator point is again a generator point. Nondegenerate generator indices are selected by
their points in the whole underlying simplicial set, whose zeroth face evaluates polynomials.
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

/-- For a commutative ring `k : Type u`, `A : CommAlgCat.{max u v} k`, and `n : ℕ`, `Index k A n`
is the carrier of `(polynomialPower k n).obj A`, namely `T^n A` for the polynomial comonad
`T`. Its universe is `max u v`. -/
abbrev Index (n : ℕ) : Type (max u v) := (polynomialPower.{u, v} k n).obj A

/-- Let `k : Type u` be a commutative ring and `A : CommAlgCat.{max u v} k`. The simplicial set
`underlying k A` is the entire polynomial-resolution simplicial algebra followed by `forget
(CommAlgCat k)`. In degree `n` it has all elements of `T^{n+1}A`, and its faces include the
outer polynomial evaluation map. -/
abbrev underlying : SSet.{max u v} :=
  resolution k A ⋙ forget (CommAlgCat.{max u v} k)

/-- Let `k : Type u` be a commutative ring, `A : CommAlgCat.{max u v} k`, and `n : ℕ`. For `x∈T^n
A`, `point k A n x` is the canonical polynomial generator in degree `n` of the resolution `P`,
where `P_n ≅ Free_k(T^n A)`. Under this identification it is the variable indexed by `x`. -/
def point (n : ℕ) (x : Index k A n) : (resolution k A).obj (op ⦋n⦌) :=
  polynomialResolutionGenerator.{u, v} k A n x

/-- Let `k` be a commutative ring, `A` a `k`-algebra, and `T` the polynomial comonad. The algebra
morphism `indexHom k A n : P_n → T^n A` is the degree-object identification `P_n ≅ T(T^n A)`
followed by the polynomial-comonad counit at `T^n A`. Thus it evaluates each variable indexed
by `x` to `x`. -/
def indexHom (n : ℕ) : (resolution k A).obj (op ⦋n⦌) ⟶
    (polynomialPower.{u, v} k n).obj A :=
  (polynomialResolutionObjIso.{u, v} k A n).hom ≫
    (polynomialComonad.{u, v} k).ε.app ((polynomialPower.{u, v} k n).obj A)

/-- For a commutative ring `k`, a `k`-algebra `A`, `n : ℕ`, and `x∈Index k A n=T^n A`, `indexHom k
A n (point k A n x)=x`. The evaluation map retracts the canonical generator-point inclusion. -/
@[simp]
theorem indexHom_point (n : ℕ) (x : Index k A n) :
    (indexHom k A n).hom (point k A n x) = x := by
  change ((polynomialComonad.{u, v} k).ε.app ((polynomialPower.{u, v} k n).obj A)).hom
    ((polynomialResolutionObjIso.{u, v} k A n).hom.hom
      (polynomialResolutionGenerator.{u, v} k A n x)) = x
  rw [polynomialResolutionObjIso_hom_generator, polynomialComonad_counit_X]

/-- For a commutative ring `k`, a `k`-algebra `A`, and `n : ℕ`, the function underlying `indexHom
k A n : P_n → T^n A` is a left inverse of `point k A n : T^n A → P_n`. Equivalently,
evaluation of the point at every generator index is that index. -/
theorem indexHom_leftInverse (n : ℕ) :
    Function.LeftInverse (indexHom k A n).hom (point k A n) :=
  indexHom_point k A n

/-- For a commutative ring `k`, a `k`-algebra `A`, and every `n : ℕ`, `point k A n : T^n A → P_n`
is injective. Its left inverse is the evaluation morphism `indexHom k A n`, so equality of
generator points implies equality of their algebra indices. -/
theorem point_injective (n : ℕ) : Function.Injective (point k A n) :=
  (indexHom_leftInverse k A n).injective

/-- Let `k` be a commutative ring, `A` a `k`-algebra, and `P` its polynomial-comonad resolution.
For `y∈P_n`, `IsGenerator k A n y` means that there exists `x∈T^n A` with `y=point k A n x`,
the canonical polynomial variable at that index. -/
def IsGenerator (n : ℕ) (y : (resolution k A).obj (op ⦋n⦌)) : Prop :=
  ∃ x : Index k A n, y = point k A n x

theorem point_isGenerator (n : ℕ) (x : Index k A n) : IsGenerator k A n (point k A n x) :=
  ⟨x, rfl⟩

theorem point_indexHom {n : ℕ} {y : (resolution k A).obj (op ⦋n⦌)}
    (hy : IsGenerator k A n y) : point k A n ((indexHom k A n).hom y) = y := by
  rcases hy with ⟨x, rfl⟩
  rw [indexHom_point]

/-- Let `k` be a commutative ring, `A` a `k`-algebra, `n : ℕ`, `i : Fin(n+1)`, and `x∈T^{n+1}A`.
The face `δ_{i+1}:P_{n+1}→P_n` sends `point_{n+1}(x)` to `point_n(ε_i(x))`, where
`ε_i=Comonad.cobarEpsilonAtPos (polynomialComonad k) n i A : T^{n+1}A→T^n A` applies the
counit at the indicated position. -/
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

/-- Let `k` be a commutative ring, `A` a `k`-algebra, `n : ℕ`, `i : Fin(n+1)`, and `y∈P_n`. If the
degeneracy image `σ_i(y)∈P_{n+1}` is a canonical polynomial generator point, then `y` is a
canonical generator point in degree `n`. The positive face `δ_{i+1}` retracts this degeneracy. -/
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

/-- Let `k` be a commutative ring, `A` a `k`-algebra, and `e : [n] → [m]` an epimorphism in the
simplex category. If `y∈P_m` is a generator point, then `P(e.op)(y)∈P_n` is a generator point.
The map is the composite of algebra degeneracies in the polynomial resolution. -/
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

/-- Let `k` be a commutative ring, `A` a `k`-algebra, `e : [n] → [m]` a simplex epimorphism, and
`y∈P_m`. If `P(e.op)(y)` is a canonical polynomial generator point in degree `n`, then `y` is
a generator point in degree `m`. -/
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

/-- For a commutative ring `k : Type u`, `A : CommAlgCat.{max u v} k`, and `n : ℕ`, `Variables k A
n` is the subtype of indices `x∈T^n A` for which `point k A n x` is nondegenerate in the whole
underlying simplicial set of the polynomial resolution. Its carrier universe is `max u v`. -/
abbrev Variables (n : ℕ) : Type (max u v) :=
  {x : Index k A n // point k A n x ∈ (underlying k A).nonDegenerate n}

end CommAlgCat.CanonicalPolynomialGeneratorPoints

end
