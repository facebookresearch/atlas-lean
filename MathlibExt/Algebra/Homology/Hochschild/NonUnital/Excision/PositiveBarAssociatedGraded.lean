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
# Positive bar filtered and associated complexes

The positive relative bar kernel has zero degree-zero object and word length N in degree N >
0. Define G_p,0 = 0 and G_p,n+1 by the ideal-count stage requiring n + 1 − p ideal entries.
Its predecessor H_p is zero at p = 0 and G_(p−1) otherwise.

The positive b′ differential preserves both families. Restricting it gives filtered and
lower-stage complexes and their inclusions; descending it gives the associated complex with
terms G_p,N/H_p,N. Its projection is a chain map, its positive-degree formula is projection
after the restricted boundary, and its degree-zero term is zero.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable (k : Type u) [CommRing k] (A : Type v) [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A] (I : NonUnitalSubalgebra k A) [I.IsTwoSided]
  (V : Type w) [AddCommGroup V] [Module k V]

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. For p : ℕ,
barFullWordFiltration p is the family G_p,0 = ⊥ and G_p,n+1 = barWordFiltration p n in
positive degree n + 1. -/
def barFullWordFiltration (p : ℕ) :
    ∀ n : ℕ, Submodule k ((relativePositiveBarComplex k A I V).X n)
  | 0 => ⊥
  | n + 1 => barWordFiltration k A I V p n

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. For
filtration index p, put G_p,0 = ⊥ and G_p,n+1 = barWordFiltration p n, and put H_p,N = ⊥ at p
= 0 and G_(p−1),N otherwise. barFullLowerWordFiltration p N is H_p,N, a submodule of K_+.X N. -/
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

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. For
filtration index p, put G_p,0 = ⊥ and G_p,n+1 = barWordFiltration p n, and put H_p,N = ⊥ at p
= 0 and G_(p−1),N otherwise. For p,n : ℕ, the image of G_p,n+1 under K_+.d (n + 1) n lies in
G_p,n. At n = 0 the target is the zero degree-zero stage. -/
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

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. For
filtration index p, put G_p,0 = ⊥ and G_p,n+1 = barWordFiltration p n, and put H_p,N = ⊥ at p
= 0 and G_(p−1),N otherwise. barStageD p n : G_p,n+1 →ₗ[k] G_p,n is the restriction of K_+.d
(n + 1) n. -/
def barStageD (p n : ℕ) :
    barFullWordFiltration k A I V p (n + 1) →ₗ[k] barFullWordFiltration k A I V p n :=
  LinearMap.codRestrict (barFullWordFiltration k A I V p n)
    (((relativePositiveBarComplex k A I V).d (n + 1) n).hom.domRestrict
      (barFullWordFiltration k A I V p (n + 1)))
    (fun x => (Submodule.map_le_iff_le_comap.mp
      (barFullWordFiltration_d k A I V p n)) x.property)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. For
filtration index p, put G_p,0 = ⊥ and G_p,n+1 = barWordFiltration p n, and put H_p,N = ⊥ at p
= 0 and G_(p−1),N otherwise. barLowerStageD p n : H_p,n+1 →ₗ[k] H_p,n is the restricted
relative positive bar boundary. -/
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

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. For
filtration index p, put G_p,0 = ⊥ and G_p,n+1 = barWordFiltration p n, and put H_p,N = ⊥ at p
= 0 and G_(p−1),N otherwise. barFilteredWordComplex p has degree-N module G_p,N and
differential barStageD p n from n + 1 to n. -/
def barFilteredWordComplex (p : ℕ) : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of k (barFullWordFiltration k A I V p n))
    (fun n => ModuleCat.ofHom (barStageD k A I V p n)) (by exact barStageD_square k A I V p)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. For
filtration index p, put G_p,0 = ⊥ and G_p,n+1 = barWordFiltration p n, and put H_p,N = ⊥ at p
= 0 and G_(p−1),N otherwise. barLowerWordComplex p has degree-N module H_p,N and differential
barLowerStageD p n. -/
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

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. For
filtration index p, put G_p,0 = ⊥ and G_p,n+1 = barWordFiltration p n, and put H_p,N = ⊥ at p
= 0 and G_(p−1),N otherwise. For x : G_p,n+1, inclusion of (barFilteredWordComplex p).d (n +
1) n x into K_+.X n equals K_+.d (n + 1) n x.val. -/
theorem barFilteredWordComplex_d_val (p n : ℕ)
    (x : barFullWordFiltration k A I V p (n + 1)) :
    (barFullWordFiltration k A I V p n).subtype
      (((barFilteredWordComplex k A I V p).d (n + 1) n).hom x) =
      ((relativePositiveBarComplex k A I V).d (n + 1) n).hom x.val := by
  rw [barFilteredWordComplex_d]
  rfl

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. For
filtration index p, put G_p,0 = ⊥ and G_p,n+1 = barWordFiltration p n, and put H_p,N = ⊥ at p
= 0 and G_(p−1),N otherwise. barFilteredWordInclusion p : barFilteredWordComplex p ⟶ K_+ has
component G_p,N.subtype in every degree N. -/
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

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. For
filtration index p, put G_p,0 = ⊥ and G_p,n+1 = barWordFiltration p n, and put H_p,N = ⊥ at p
= 0 and G_(p−1),N otherwise. barLowerWordInclusion p maps barLowerWordComplex p to
barFilteredWordComplex p using H_p,N ≤ G_p,N in each degree. -/
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

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. For
filtration index p, put G_p,0 = ⊥ and G_p,n+1 = barWordFiltration p n, and put H_p,N = ⊥ at p
= 0 and G_(p−1),N otherwise. For p ≤ q, barFilteredWordMap maps barFilteredWordComplex p to
barFilteredWordComplex q by the component inclusions G_p,N ≤ G_q,N. -/
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

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. For
filtration index p, put G_p,0 = ⊥ and G_p,n+1 = barWordFiltration p n, and put H_p,N = ⊥ at p
= 0 and G_(p−1),N otherwise. barFullWordLayer p N is G_p,N modulo the inverse image of H_p,N
under G_p,N.subtype. This definition includes degree zero. -/
abbrev barFullWordLayer (p n : ℕ) :=
  barFullWordFiltration k A I V p n ⧸
    (barFullLowerWordFiltration k A I V p n).comap
      (barFullWordFiltration k A I V p n).subtype

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. For
filtration index p, put G_p,0 = ⊥ and G_p,n+1 = barWordFiltration p n, and put H_p,N = ⊥ at p
= 0 and G_(p−1),N otherwise. barFullWordLayerProjection p N is the k-linear quotient map G_p,N
→ G_p,N/H_p,N, with H_p,N viewed inside G_p,N. -/
def barFullWordLayerProjection (p n : ℕ) :
    barFullWordFiltration k A I V p n →ₗ[k] barFullWordLayer k A I V p n :=
  ((barFullLowerWordFiltration k A I V p n).comap
    (barFullWordFiltration k A I V p n).subtype).mkQ

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. For
filtration index p, put G_p,0 = ⊥ and G_p,n+1 = barWordFiltration p n, and put H_p,N = ⊥ at p
= 0 and G_(p−1),N otherwise. barLayerD p n maps the full layer at n + 1 to the full layer at n
by the quotient map induced from barStageD p n and predecessor preservation. -/
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

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. For
filtration index p, put G_p,0 = ⊥ and G_p,n+1 = barWordFiltration p n, and put H_p,N = ⊥ at p
= 0 and G_(p−1),N otherwise. barAssociatedWordComplex p has degree-N term barFullWordLayer p N
and successor differential barLayerD p n. -/
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

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. For
filtration index p, put G_p,0 = ⊥ and G_p,n+1 = barWordFiltration p n, and put H_p,N = ⊥ at p
= 0 and G_(p−1),N otherwise. barAssociatedWordProjection p : barFilteredWordComplex p ⟶
barAssociatedWordComplex p has degree-N component barFullWordLayerProjection p N. -/
def barAssociatedWordProjection (p : ℕ) :
    barFilteredWordComplex k A I V p ⟶ barAssociatedWordComplex k A I V p :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (barFullWordLayerProjection k A I V p n))
    (fun n => by
      rw [barFilteredWordComplex_d, barAssociatedWordComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact barLayerD_projection k A I V p n x)

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. For
filtration index p, put G_p,0 = ⊥ and G_p,n+1 = barWordFiltration p n, and put H_p,N = ⊥ at p
= 0 and G_(p−1),N otherwise. For x : barWordFiltration p (n + 1), in degree n + 2, the
associated differential of [x] is the layer projection of the filtered boundary in degree n +
1. -/
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

/-- Let k be commutative, A a nonunital k-algebra ring with k-bilinear multiplication, I two-sided
and V an arbitrary k-module. Let K_+ be the relative positive bar quotient kernel. For
filtration index p, put G_p,0 = ⊥ and G_p,n+1 = barWordFiltration p n, and put H_p,N = ⊥ at p
= 0 and G_(p−1),N otherwise. For every p : ℕ, (barAssociatedWordComplex p).X 0 is a zero
object, because both the full stage and its quotient have zero ambient carrier in that degree. -/
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
