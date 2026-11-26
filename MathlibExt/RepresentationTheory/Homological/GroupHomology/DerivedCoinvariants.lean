/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic

/-!
# Left-derived coinvariants of the trivial representation

For a commutative ring k and monoid G, tensoring on the left by k_triv
before coinvariants is naturally isomorphic to coinvariants:
(k_triv⊗A)_G≅A_G. The comparison is induced by the tensor left unitor
and extends degreewise to any nonnegative chain complex of representations.

For a group G and ring k in universe u, with enough projectives in
Rep.{u} k G, the bar resolution gives
L_n((-)_G)(k_triv)≅H_n(G,k_triv).
The intervening chain comparison is the same tensor-unit coinvariant
isomorphism. All degrees n∈ℕ are included.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe u v

open CategoryTheory

namespace Rep

variable (k : Type u) (G : Type v) [CommRing k] [Monoid G]

/-- Let k be a commutative ring in universe u and G a monoid in
universe v. Let k_triv be the trivial representation and (-)_G the
coinvariant functor on k-linear G-representations.
The natural isomorphism (k_triv⊗A)_G≅A_G is induced by
the tensor left unitor k_triv⊗A→A. -/
noncomputable def coinvariantsTensorTrivialNatIso :
    (coinvariantsTensor k G).obj (trivial k G k) ≅ coinvariantsFunctor k G :=
  Functor.isoWhiskerRight (MonoidalCategory.leftUnitorNatIso (Rep.{u} k G))
      (coinvariantsFunctor k G) ≪≫
    Functor.leftUnitor (coinvariantsFunctor k G)

/-- Let k be a commutative ring in universe u and G a monoid in
universe v. Let k_triv be the trivial representation and (-)_G the
coinvariant functor on k-linear G-representations.
The forward component at A is the coinvariant map of the
left unitor, sending the class of r⊗a to the class of r•a. -/
@[simp]
theorem coinvariantsTensorTrivialNatIso_hom_app (A : Rep.{u} k G) :
    (coinvariantsTensorTrivialNatIso k G).hom.app A =
      (coinvariantsFunctor k G).map (MonoidalCategory.leftUnitor A).hom :=
  rfl

end Rep

namespace HomologicalComplex

variable (k : Type u) (G : Type v) [CommRing k] [Monoid G]

/-- Let k be a commutative ring in universe u and G a monoid in
universe v. Let k_triv be the trivial representation and (-)_G the
coinvariant functor on k-linear G-representations.
For a nonnegative chain complex K of representations,
the degreewise tensor-unit coinvariant maps give the chain isomorphism
(k_triv⊗K)_G≅K_G. -/
noncomputable def coinvariantsTensorTrivialIso
    (K : ChainComplex (Rep.{u} k G) ℕ) :
    (((Rep.coinvariantsTensor k G).obj
        (Rep.trivial k G k)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj K ≅
      ((Rep.coinvariantsFunctor k G).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj K :=
  (NatIso.mapHomologicalComplex (Rep.coinvariantsTensorTrivialNatIso k G)
    (ComplexShape.down ℕ)).app K

/-- Let k be a commutative ring in universe u and G a monoid in
universe v. Let k_triv be the trivial representation and (-)_G the
coinvariant functor on k-linear G-representations.
In degree n, the forward chain component is the coinvariant
map of k_triv⊗K_n→K_n, the left tensor unitor. -/
@[simp]
theorem coinvariantsTensorTrivialIso_hom_f
    (K : ChainComplex (Rep.{u} k G) ℕ) (n : ℕ) :
    (coinvariantsTensorTrivialIso k G K).hom.f n =
      (Rep.coinvariantsFunctor k G).map
        (MonoidalCategory.leftUnitor (K.X n)).hom :=
  rfl

end HomologicalComplex

namespace groupHomology

variable (k G : Type u) [CommRing k] [Group G]
  [EnoughProjectives (Rep.{u} k G)]

/-- For a commutative ring k and group G in universe u, the bar
resolution P of k_triv computes the isomorphism
H_n(G,k_triv)≅H_n((k_triv⊗P)_G) for every n∈ℕ. -/
noncomputable def trivialBarResolutionIso (n : ℕ) :
    groupHomology (Rep.trivial k G k) n ≅
      ((Rep.barResolution k G).complex.coinvariantsTensorObj
        (Rep.trivial k G k)).homology n := by
  classical
  exact groupHomologyIso (Rep.trivial k G k) n (Rep.barResolution k G)

/-- Let k,G have universe u, with k a commutative ring and G a group.
Assume enough projectives in Rep.{u} k G. Write P for the bar resolution
of the trivial representation k_triv and F=(-)_G for coinvariants.
The object-level comparison is
L_nF(k_triv)≅H_n(G,k_triv), through the bar resolution and
the tensor-unit comparison of its coinvariant complexes. -/
noncomputable def leftDerivedCoinvariantsTrivialIso (n : ℕ) :
    ((Rep.coinvariantsFunctor k G).leftDerived n).obj
        (Rep.trivial k G k) ≅
      groupHomology (Rep.trivial k G k) n :=
  (Rep.barResolution k G).isoLeftDerivedObj (Rep.coinvariantsFunctor k G) n ≪≫
    ((HomologicalComplex.homologyFunctor (ModuleCat k)
      (ComplexShape.down ℕ) n).mapIso
        (HomologicalComplex.coinvariantsTensorTrivialIso k G
          (Rep.barResolution k G).complex)).symm ≪≫
    (trivialBarResolutionIso k G n).symm

/-- Let k,G have universe u, with k a commutative ring and G a group.
Assume enough projectives in Rep.{u} k G. Write P for the bar resolution
of the trivial representation k_triv and F=(-)_G for coinvariants.
The forward comparison first maps L_nF(k_triv) to H_n(F(P)),
then uses the inverse tensor-unit chain homology map to
H_n((k_triv⊗P)_G), and finally the inverse bar-resolution group-homology
comparison. -/
theorem leftDerivedCoinvariantsTrivialIso_hom (n : ℕ) :
    (leftDerivedCoinvariantsTrivialIso k G n).hom =
      ((Rep.barResolution k G).isoLeftDerivedObj
        (Rep.coinvariantsFunctor k G) n).hom ≫
        ((HomologicalComplex.homologyFunctor (ModuleCat k)
          (ComplexShape.down ℕ) n).mapIso
            (HomologicalComplex.coinvariantsTensorTrivialIso k G
              (Rep.barResolution k G).complex)).inv ≫
        (trivialBarResolutionIso k G n).inv :=
  rfl

end groupHomology

end
