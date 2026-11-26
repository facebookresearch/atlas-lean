/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.CanonicalPolynomialGeneratorPoints
public import Mathlib.AlgebraicTopology.SimplicialSet.Splitting
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Nondegenerate decomposition of canonical polynomial generators

Let `k : Type u` be a commutative ring and `A : CommAlgCat.{max u v} k`. Write `T` for the
polynomial comonad and `P` for its simplicial resolution, with `P_n ≅ T^{n+1}A`. Polynomial
generators in degree `n` are indexed by the carrier of `T^n A`; evaluation retracts their
inclusion.

Every generator index is the image under a unique simplex epimorphism `[n] → [m]` of a unique
index whose generator point is nondegenerate in the whole underlying simplicial set. This
gives a coproduct decomposition of the degree-`n` generator-index type by the
epimorphism-indexed nondegenerate generator types.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialObject.Splitting
open scoped Simplicial

universe u v

namespace CommAlgCat.CanonicalPolynomialGeneratorDecomposition

open CanonicalPolynomialGeneratorPoints

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/-- Let `k : Type u` be a commutative ring, `A : CommAlgCat.{max u v} k`, and `P` its
polynomial-comonad resolution. For an epimorphism `e : [n] → [m]` and an index `x∈T^m A`,
`epiIndex k A e x` is `indexHom_n(P(e.op)(point_m x)) ∈ T^n A`. Here `point_m` includes a
polynomial generator and `indexHom_n` evaluates the outer polynomial layer. -/
def epiIndex {n m : ℕ} (e : ⦋n⦌ ⟶ ⦋m⦌) [Epi e] (x : Index k A m) : Index k A n :=
  (indexHom k A n).hom (((resolution k A).map e.op).hom (point k A m x))

theorem point_epiIndex {n m : ℕ} (e : ⦋n⦌ ⟶ ⦋m⦌) [Epi e] (x : Index k A m) :
    point k A n (epiIndex k A e x) = ((resolution k A).map e.op).hom (point k A m x) :=
  point_indexHom k A (epi_image_generator k A e _ (point_isGenerator k A m x))

def nondegeneratePoint (n : ℕ) (x : Variables k A n) : (underlying k A).nonDegenerate n :=
  ⟨point k A n x.val, x.property⟩

/-- For a commutative ring `k`, an algebra `A`, and degree `n`, let `a` be an Eilenberg–Zilber
index consisting of an epimorphism `a.e : [n] → [m]`. For `x∈Variables_m`, an index whose
degree-`m` generator point is nondegenerate in the underlying polynomial resolution,
`summandIndex k A a x = epiIndex k A a.e x.val` is the resulting degree-`n` generator index. -/
def summandIndex {n : ℕ} (a : IndexSet (op ⦋n⦌)) (x : Variables k A a.1.unop.len) :
    Index k A n := epiIndex k A a.e x.val

theorem point_summandIndex {n : ℕ} (a : IndexSet (op ⦋n⦌))
    (x : Variables k A a.1.unop.len) :
    point k A n (summandIndex k A a x) =
      ((resolution k A).map a.e.op).hom (point k A a.1.unop.len x.val) :=
  point_epiIndex k A a.e x.val

/-- Let `k` be a commutative ring, `A` a `k`-algebra in carrier universe `max u v`, `T` the
polynomial comonad, and `n : ℕ`. For every `x∈T^n A`, there exist an epimorphism index `a :
[n] → [m]` and `y∈Variables_m` such that `summandIndex k A a y=x`. The set `Variables_m`
consists of indices whose generator points are nondegenerate in the whole underlying
simplicial resolution. -/
theorem jointly_surjective (n : ℕ) (x : Index k A n) :
    ∃ (a : IndexSet (op ⦋n⦌)) (y : Variables k A a.1.unop.len), summandIndex k A a y = x := by
  obtain ⟨m, e, he, y, hy⟩ := (underlying k A).exists_nonDegenerate (point k A n x)
  letI : Epi e := he
  have hgen : IsGenerator k A m y.val := epi_preimage_generator k A e y.val (by
    change IsGenerator k A n ((underlying k A).map e.op y)
    rw [← hy]
    exact point_isGenerator k A n x)
  obtain ⟨z, hz⟩ := hgen
  let w : Variables k A m := ⟨z, by rw [← hz]; exact y.property⟩
  refine ⟨IndexSet.mk e, w, ?_⟩
  apply point_injective k A n
  have hS := point_summandIndex k A (IndexSet.mk e) w
  have hY := congrArg (fun a => (underlying k A).map e.op a) hz
  exact hS.trans (hY.symm.trans hy.symm)

/-- Let `k` be a commutative ring, `A` a `k`-algebra, and `a` an epimorphism index `[n] → [m]` in
the polynomial resolution's Eilenberg–Zilber decomposition. The map `summandIndex k A a :
Variables_m → T^n A` is injective. Thus a fixed epimorphism determines its nondegenerate
generator index uniquely. -/
theorem summand_injective {n : ℕ} (a : IndexSet (op ⦋n⦌)) :
    Function.Injective (summandIndex k A a) := by
  intro x y h
  have hpt₀ := congrArg (point k A n) h
  have hpt := (point_summandIndex k A _ _).symm.trans
    (hpt₀.trans (point_summandIndex k A _ _))
  have hnd := (underlying k A).unique_nonDegenerate_simplex
    ((underlying k A).map a.e.op (nondegeneratePoint k A a.1.unop.len x))
    a.e (nondegeneratePoint k A a.1.unop.len x) rfl
    a.e (nondegeneratePoint k A a.1.unop.len y) hpt
  apply Subtype.ext
  exact point_injective k A a.1.unop.len (congrArg Subtype.val hnd)

/-- Let `k` be a commutative ring, `A` a `k`-algebra, and `a,b` epimorphism indices with source
`[n]`. For nondegenerate generator indices `x∈Variables_{target(a)}` and
`y∈Variables_{target(b)}`, if `summandIndex k A a x = summandIndex k A b y`, then `a=b`.
Equality determines the full epimorphism index, including its target and map. -/
theorem summand_eq {n : ℕ} (a b : IndexSet (op ⦋n⦌))
    (x : Variables k A a.1.unop.len) (y : Variables k A b.1.unop.len)
    (h : summandIndex k A a x = summandIndex k A b y) : a = b := by
  rcases a with ⟨⟨⟨m⟩⟩, e, he⟩
  rcases b with ⟨⟨⟨l⟩⟩, f, hf⟩
  letI : Epi e := he
  letI : Epi f := hf
  have hpt₀ := congrArg (point k A n) h
  have hpt := (point_summandIndex k A _ _).symm.trans
    (hpt₀.trans (point_summandIndex k A _ _))
  have hd : m = l := (underlying k A).unique_nonDegenerate_dim
    ((underlying k A).map e.op (nondegeneratePoint k A m x))
    e (nondegeneratePoint k A m x) rfl f (nondegeneratePoint k A l y) hpt
  subst l
  have hef : e = f := (underlying k A).unique_nonDegenerate_map
    ((underlying k A).map e.op (nondegeneratePoint k A m x))
    e (nondegeneratePoint k A m x) rfl f (nondegeneratePoint k A m y) hpt
  subst f
  rfl

/-- Let `k` be a commutative ring, `A` a `k`-algebra, and `n : ℕ`. The cofan `generatorCofan k A
n` in the category of types has point `T^n A`, summands `Variables_m` indexed by all
epimorphisms `a : [n] → [m]`, and injection `summandIndex k A a`. It is the coproduct
decomposition of the generator-index type by nondegenerate ancestors. -/
def generatorCofan (n : ℕ) : Cofan (fun a : IndexSet (op ⦋n⦌) => Variables k A a.1.unop.len) :=
  Cofan.mk (Index k A n) (fun a => TypeCat.ofHom (summandIndex k A a))

def generatorCofanIsColimit (n : ℕ) : IsColimit (generatorCofan k A n) :=
  Nonempty.some (by
    rw [← Cofan.isColimit_cofanTypes_iff]
    refine CofanTypes.isColimit_mk _ ?_ ?_ ?_
    · exact jointly_surjective k A n
    · intro a x y h
      exact summand_injective k A a h
    · intro a b x y h
      exact summand_eq k A a b x y h)

end CommAlgCat.CanonicalPolynomialGeneratorDecomposition

end
