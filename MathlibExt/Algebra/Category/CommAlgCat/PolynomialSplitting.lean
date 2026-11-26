/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.CommAlgCat.Free
public import Mathlib.AlgebraicTopology.SimplicialSet.Splitting
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Polynomial coordinates on nondegenerate simplicial summands

Let `k : Type u` be a commutative ring and `P` a simplicial `k`-algebra of carrier universe
`max u v`. A `PolynomialSplitting` consists of a simplicial coproduct splitting over simplex
epimorphisms, with each nondegenerate summand `N_n` identified as a polynomial algebra on a
type of variables.

Assignments of these variables to a target simplicial algebra extend by polynomial evaluation
on each summand and by the coproduct universal property in each degree. The resulting degree
maps satisfy naturality for simplex epimorphisms, hence for degeneracies.

Applying the free-algebra functor to a simplicial set gives this structure, with variable
types the nondegenerate simplices.

## References

* Stacks Project, Tag 017O.
* J.-L. Loday, *Cyclic Homology*, 3.5.1–3.5.2, for degeneracy-compatible polynomial generators.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v

namespace CommAlgCat

variable (k : Type u) [CommRing k]

/-- Let `k : Type u` be a commutative ring and `P : SimplicialObject (CommAlgCat.{max u v} k)`. A
`PolynomialSplitting k P` contains a splitting `P.Splitting`, variable types `V_n`, and
isomorphisms `N_n ≅ MvPolynomial V_n k` for its nondegenerate summands. The splitting
expresses each `P_n` as a coproduct of the `N_m` indexed by simplex epimorphisms `[n] → [m]`. -/
structure PolynomialSplitting (P : SimplicialObject (CommAlgCat.{max u v} k)) where
  splitting : P.Splitting
  «variables» : ℕ → Type (max u v)
  polynomialIso : ∀ n, splitting.N n ≅ CommAlgCat.of k (MvPolynomial («variables» n) k)

namespace PolynomialSplitting

variable {k} {P Q : SimplicialObject (CommAlgCat.{max u v} k)}
  (s : PolynomialSplitting k P) (y : ∀ n, s.variables n → Q.obj (op ⦋n⦌))

/-- Let `s : PolynomialSplitting k P`, `Q` a target simplicial `k`-algebra, and `y_n : s.variables
n → Q_n` arbitrary assignments. The morphism `s.generatorMap y n : s.splitting.N n → Q_n` is
`s.polynomialIso n` followed by polynomial evaluation at `y_n`. It extends the chosen images
of all nondegenerate polynomial variables. -/
def generatorMap (n : ℕ) : s.splitting.N n ⟶ Q.obj (op ⦋n⦌) :=
  (s.polynomialIso n).hom ≫ CommAlgCat.ofHom (MvPolynomial.aeval (y n))

/-- Let `s : PolynomialSplitting k P`, `Q` a simplicial `k`-algebra, and assignments `y_n` of the
variables of each nondegenerate summand to `Q_n`. For `Δ : SimplexCategoryᵒᵖ`, `s.degreeMap y
Δ : P(Δ) → Q(Δ)` is the coproduct descendant with summand map `s.generatorMap y m ≫ Q(a.e.op)`
at each epimorphism index `a` with target degree `m`. -/
def degreeMap (Δ : SimplexCategoryᵒᵖ) : P.obj Δ ⟶ Q.obj Δ :=
  s.splitting.desc Δ (fun a => s.generatorMap y a.1.unop.len ≫ Q.map a.e.op)

/-- Let `s : PolynomialSplitting k P`, `Q` a simplicial `k`-algebra, and `y_n` assignments of the
nondegenerate polynomial variables to `Q_n`. For `Δ` and an epimorphism index `a` of target
degree `m`, `(s.splitting.cofan Δ).inj a ≫ s.degreeMap y Δ = s.generatorMap y m ≫ Q.map
a.e.op`. This identifies each coproduct summand of the degree map. -/
@[reassoc]
theorem summand_degreeMap (Δ : SimplexCategoryᵒᵖ) (a : SimplicialObject.Splitting.IndexSet Δ) :
    (s.splitting.cofan Δ).inj a ≫ s.degreeMap y Δ =
      s.generatorMap y a.1.unop.len ≫ Q.map a.e.op :=
  s.splitting.ι_desc Δ _ a

/-- For `s : PolynomialSplitting k P`, a target simplicial algebra `Q`, variable assignments
`y_n`, and `n : ℕ`, `s.splitting.ι n ≫ s.degreeMap y (op [n]) = s.generatorMap y n`. The
degree map uses the prescribed generator images on the distinguished nondegenerate summand. -/
@[reassoc]
theorem distinguished_degreeMap (n : ℕ) :
    s.splitting.ι n ≫ s.degreeMap y (op ⦋n⦌) = s.generatorMap y n := by
  have h := s.summand_degreeMap y (op ⦋n⦌) (SimplicialObject.Splitting.IndexSet.id _)
  rw [s.splitting.cofan_inj_id n] at h
  change s.splitting.ι n ≫ s.degreeMap y (op ⦋n⦌) =
    s.generatorMap y n ≫ Q.map (𝟙 (op ⦋n⦌)) at h
  exact h.trans ((congrArg (fun f => s.generatorMap y n ≫ f) (Q.map_id (op ⦋n⦌))).trans
    (Category.comp_id _))

/-- Let `s : PolynomialSplitting k P`, `Q` a simplicial `k`-algebra, and `y_n` arbitrary
nondegenerate-variable assignments. For `θ : Δ → Δ'` in `SimplexCategoryᵒᵖ` with `Epi θ.unop`,
`P.map θ ≫ s.degreeMap y Δ' = s.degreeMap y Δ ≫ Q.map θ`. Thus the degree maps are natural for
the degeneracy maps represented by simplex epimorphisms. -/
theorem degreeMap_epi_naturality {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') [Epi θ.unop] :
    P.map θ ≫ s.degreeMap y Δ' = s.degreeMap y Δ ≫ Q.map θ := by
  apply s.splitting.hom_ext'
  intro a
  have hNat := s.splitting.cofan_inj_epi_naturality a θ
  have hNew := s.summand_degreeMap y Δ' (a.epiComp θ)
  have hOld := s.summand_degreeMap y Δ a
  dsimp only [SimplicialObject.Splitting.IndexSet.epiComp] at hNew
  have hF : Q.map (a.epiComp θ).e.op = Q.map a.e.op ≫ Q.map θ := by
    change Q.map (a.e.op ≫ θ) = Q.map a.e.op ≫ Q.map θ
    exact Q.map_comp _ _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ s.degreeMap y Δ') hNat).trans
      (hNew.trans
        ((congrArg (fun f => s.generatorMap y a.1.unop.len ≫ f) hF).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun f => f ≫ Q.map θ) hOld.symm).trans
              (Category.assoc _ _ _))))))

end PolynomialSplitting

/-- For a commutative ring `k : Type u` and `X : SSet.{max u v}`, the simplicial algebra `X ⋙ free
k` has a `PolynomialSplitting`. Its splitting is the Eilenberg–Zilber splitting of `X` mapped
by the free-algebra functor, its degree-`n` variable type is `X.nonDegenerate n`, and each
nondegenerate polynomial coordinate isomorphism is the identity. -/
def polynomialSplittingOfSSet (X : SSet.{max u v}) :
    PolynomialSplitting k (X ⋙ free.{u, v} k) where
  splitting := X.splitting.map (free.{u, v} k)
  «variables» n := X.nonDegenerate n
  polynomialIso n := Iso.refl _

end CommAlgCat

end
