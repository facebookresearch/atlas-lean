/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import MathlibExt.AlgebraicGeometry.NeronModels

/-!
# Grothendieck's semistable reduction theorem

An abelian variety over a field `F` is an abelian scheme over `Spec F`. For a discrete
valuation ring `R` with fraction field `F` and residue field `k`, the abelian variety `X` has
semistable reduction at `R` when it has a Néron model `𝒳` over `R`, a commutative group scheme
whose group law extends that of `X`, such that the identity component `X⁰ᵥ` of the special fibre
`𝒳 ⊗_R k` is an extension of an abelian variety by an affine torus. A torus over `k` is a group
scheme that becomes isomorphic, over an algebraic closure of `k`, to a split torus
`Spec k̄[ℤʳ]` with its Hopf-algebra group law.

The theorem: for every abelian variety over a field with a discrete valuation, there is a finite
Galois extension over which it has semistable reduction at every extension of the valuation.

Source: A. Silverberg and Yu. G. Zarhin, *Semistable reduction and torsion subgroups of abelian
varieties*, Ann. Inst. Fourier 45 (1995), 403–420, §3, pp. 404–405 (the Néron model and
Definition 3.1 (ii)) and Theorem 3.4, pp. 405–406, <https://doi.org/10.5802/aif.1459>. For the
proof they cite A. Grothendieck, *Modèles de Néron et monodromie*, SGA 7 I, Exp. IX, Lecture Notes
in Math. 288, Springer, 1972, 313–523, Théorème 3.6, which they call Proposition 3.6. The same
theorem, with a finite separable extension, is Theorem 4.2 of B. Conrad, *Semistable reduction for
abelian varieties*, seminar notes, Stanford, 2011.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.SemistableReductionWanted

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AbelianSchemes
open MathlibExt.AlgebraicGeometry.NeronModels
open MathlibExt.AlgebraicGeometry.SemistableModels

universe u

section Field

variable (k : Type u) [Field k]

/-- The split torus `𝔾ₘʳ = Spec k[ℤʳ]` over a field `k`, with the group law of the Hopf algebra
`k[ℤʳ]`. -/
abbrev splitTorus (r : ℕ) : Over (Spec (.of k)) :=
  (Spec (.of (AddMonoidAlgebra k (Fin r → ℤ)))).asOver (Spec (.of k))

variable {k}

/-- A torus over a field `k`: a group scheme `T` over `k` whose base change to an algebraic
closure `k̄` of `k` is isomorphic, as a group scheme, to a split torus `Spec k̄[ℤʳ]`. -/
def IsTorus (T : Over (Spec (.of k))) [GrpObj T] : Prop :=
  ∃ (r : ℕ) (e : (Over.pullback (Spec.map (CommRingCat.ofHom
      (algebraMap k (AlgebraicClosure k))))).obj T ≅ splitTorus (AlgebraicClosure k) r),
    IsMonHom e.hom

/-- A group scheme `G` over a field `k` is an extension of an abelian variety by a torus: there
are a torus `T`, an abelian variety `B` and homomorphisms `T → G → B` with `G → B` faithfully
flat and `T` its kernel, the fibre of `G → B` over the zero section of `B`. -/
def IsExtensionOfAbelianVarietyByTorus (G : Over (Spec (.of k))) [GrpObj G] : Prop :=
  ∃ (T : Over (Spec (.of k))) (_ : GrpObj T) (B : AbelianScheme (Spec (.of k)))
    (i : T ⟶ G) (p : G ⟶ B.model),
    IsTorus T ∧ IsMonHom i ∧ IsMonHom p ∧ Flat p.left ∧ Surjective p.left ∧
      IsPullback i (toUnit T) p η[B.model]

/-- `j : G⁰ → G` is the identity component of a group scheme `G` over a field: a homomorphism
that is an open immersion whose image is the connected component of the identity point. -/
def IsIdentityComponent {G₀ G : Over (Spec (.of k))} [GrpObj G₀] [GrpObj G] (j : G₀ ⟶ G) :
    Prop :=
  IsOpenImmersion j.left ∧ IsMonHom j ∧
    ∀ x : (𝟙_ (Over (Spec (.of k)))).left,
      Set.range j.left = connectedComponent (η[G].left x)

end Field

/-- **Semistable reduction** (Silverberg–Zarhin, §3, pp. 404–405, Definition 3.1 (ii)). Let `R`
be a discrete valuation ring with fraction field `K` and residue field `k`. An abelian variety
`X` over `K` has semistable reduction at `R` if it has a Néron model `𝒳` over `R`, with a
commutative group law extending that of `X`, such that the identity component `X⁰ᵥ` of the
special fibre `Xᵥ = 𝒳 ⊗_R k` is an extension of an abelian variety by an affine torus. The Néron
model is taken of finite type over `R`, as in Bosch–Lütkebohmert–Raynaud, *Néron Models*, §1.2,
Definition 1; Néron models and their group laws are unique up to unique isomorphism, so this does
not depend on the choice. -/
def HasSemistableReduction (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] (X : AbelianScheme (Spec (.of K))) :
    Prop :=
  ∃ (N : FiniteTypeNeronModel R K X.model) (_ : N.GroupStructure)
    (G₀ : Over (specialBase R)) (_ : GrpObj G₀)
    (j : G₀ ⟶ (specialFunctor R).obj N.model),
    IsIdentityComponent j ∧ IsExtensionOfAbelianVarietyByTorus G₀

/-- **Grothendieck's semistable reduction theorem** (Silverberg–Zarhin, Theorem 3.4,
pp. 405–406). Let `X` be an abelian variety over a field `F` and `v` a discrete valuation on `F`,
with valuation ring `O`. There is a finite Galois extension `L` of `F`, here inside an algebraic
closure of `F`, such that `X_L` has semistable reduction at every extension of `v` to `L`: at
every valuation ring `w` of `L` with `w ∩ F = O`. Every such `w` is a discrete valuation ring, so
taking its discrete-valuation-ring structure as an instance argument loses nothing.

Source: A. Silverberg and Yu. G. Zarhin, *Semistable reduction and torsion subgroups of abelian
varieties*, Ann. Inst. Fourier 45 (1995), 403–420, Theorem 3.4, pp. 405–406,
<https://doi.org/10.5802/aif.1459>; for the proof they cite SGA 7 I, Exp. IX, Théorème 3.6, which
they call Proposition 3.6. -/
theorem_wanted semistable_reduction_theorem (F : Type u) [Field F] (O : ValuationSubring F)
    [IsDiscreteValuationRing O] (X : AbelianScheme (Spec (.of F))) :
    ∃ L : IntermediateField F (AlgebraicClosure F), FiniteDimensional F L ∧ IsGalois F L ∧
      ∀ w : ValuationSubring L, w.comap (algebraMap F L) = O → ∀ [IsDiscreteValuationRing w],
        HasSemistableReduction w L
          (X.baseChange (Spec.map (CommRingCat.ofHom (algebraMap F L))))

end WantedExt.AlgebraicGeometry.SemistableReductionWanted
