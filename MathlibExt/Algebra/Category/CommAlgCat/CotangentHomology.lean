/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.CommAlgCat.CotangentSimplicial
public import MathlibExt.Algebra.Category.ModuleCat.TensorBifunctor
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# André–Quillen homology with module coefficients

Let `k` be a commutative ring, `A` a commutative `k`-algebra, and `L_{A/k}` its normalized
polynomial cotangent chain model. For an `A`-module `M`, form the coefficient complex `M ⊗[A]
L_{A/k}` by tensoring each degree with `M` on the left.

Its degree-`n` homology defines `D_n(A/k; M)`. Coefficient maps induce chain maps and homology
maps, giving a functor in `M`. The base-ring, algebra-carrier, and coefficient-carrier
universes remain independent.

References: Stacks Project, Definition 92.3.2; Loday, *Cyclic Homology*, second edition,
Definition 3.5.4.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v t

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/-- The coefficient cotangent chain-complex functor.

For a commutative `k`-algebra `A`, this sends an `A`-module `M` to `M ⊗[A] L_{A/k}`, with `M`
in the left tensor factor in every degree. The target carrier universe accommodates the
independent base, algebra, and coefficient universes. -/
def cotangentCoefficientComplexFunctor :
    ModuleCat.{t} A ⥤ ChainComplex (ModuleCat.{max u v t} A) ℕ where
  obj M := (((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (cotangentComplex k A)
  map f := (NatTrans.mapHomologicalComplex
    ((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).map f)
    (ComplexShape.down ℕ)).app (cotangentComplex k A)
  map_id M := by
    rw [(ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).map_id M,
      NatTrans.mapHomologicalComplex_id]
    rfl
  map_comp f g := by
    rw [(ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).map_comp f g,
      NatTrans.mapHomologicalComplex_comp]
    rfl

/-- The André–Quillen homology functor in a fixed degree.

For `n ∈ ℕ`, this sends an `A`-module `M` to `H_n(M ⊗[A] L_{A/k})`, where `L_{A/k}` is the
normalized polynomial cotangent model. -/
def andreQuillenHomologyFunctor (n : ℕ) :
    ModuleCat.{t} A ⥤ ModuleCat.{max u v t} A :=
  cotangentCoefficientComplexFunctor k A ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{max u v t} A) (ComplexShape.down ℕ) n

/-- André–Quillen homology of a coefficient module.

For an `A`-module `M` and `n ∈ ℕ`, this is `D_n(A/k; M) = H_n(M ⊗[A] L_{A/k})`. -/
def andreQuillenHomology (M : ModuleCat.{t} A) (n : ℕ) : ModuleCat.{max u v t} A :=
  (andreQuillenHomologyFunctor k A n).obj M

/-- The André–Quillen map induced by a coefficient homomorphism.

An `A`-linear map `f : M → N` induces `D_n(A/k; M) → D_n(A/k; N)` by tensoring `f` with the
identity of the cotangent model and taking homology. -/
def andreQuillenHomologyMap {M N : ModuleCat.{t} A} (f : M ⟶ N) (n : ℕ) :
    andreQuillenHomology k A M n ⟶ andreQuillenHomology k A N n :=
  (andreQuillenHomologyFunctor k A n).map f

/-- The André–Quillen homology map of an identity coefficient map.

For every coefficient module `M` and degree `n`, the map induced by `id_M` is the identity on
`D_n(A/k; M)`. -/
@[simp]
theorem andreQuillenHomologyMap_id (M : ModuleCat.{t} A) (n : ℕ) :
    andreQuillenHomologyMap k A (𝟙 M) n = 𝟙 (andreQuillenHomology k A M n) :=
  (andreQuillenHomologyFunctor k A n).map_id M

/-- Composition of André–Quillen coefficient maps.

For `A`-linear maps `M → N → P`, the degree-`n` homology map of their composite is the
composite of the two induced homology maps. -/
theorem andreQuillenHomologyMap_comp {M N T : ModuleCat.{t} A}
    (f : M ⟶ N) (g : N ⟶ T) (n : ℕ) :
    andreQuillenHomologyMap k A (f ≫ g) n =
      andreQuillenHomologyMap k A f n ≫ andreQuillenHomologyMap k A g n :=
  (andreQuillenHomologyFunctor k A n).map_comp f g

end CommAlgCat

end
