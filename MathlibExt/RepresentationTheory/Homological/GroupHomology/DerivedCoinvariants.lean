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
# Derived coinvariants with trivial coefficients

This file compares the left-derived coinvariants of the trivial representation
with native group homology. Both sides are computed from Mathlib's same bar
resolution. The only intervening comparison is the monoidal left unitor, which
identifies `(k ⊗ P)_G` with `P_G` degreewise.

The construction is object-level. It does not assert a natural isomorphism
between the full derived coinvariants and group-homology functors, nor use a
balance theorem for `Rep.Tor`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe u v

open CategoryTheory

namespace Rep

variable (k : Type u) (G : Type v) [CommRing k] [Monoid G]

/-- Tensoring on the left by the trivial representation before taking
coinvariants is naturally isomorphic to taking coinvariants directly. -/
noncomputable def coinvariantsTensorTrivialNatIso :
    (coinvariantsTensor k G).obj (trivial k G k) ≅ coinvariantsFunctor k G :=
  Functor.isoWhiskerRight (MonoidalCategory.leftUnitorNatIso (Rep.{u} k G))
      (coinvariantsFunctor k G) ≪≫
    Functor.leftUnitor (coinvariantsFunctor k G)

/-- The forward component of `coinvariantsTensorTrivialNatIso` is induced by
the monoidal left unitor. -/
@[simp]
theorem coinvariantsTensorTrivialNatIso_hom_app (A : Rep.{u} k G) :
    (coinvariantsTensorTrivialNatIso k G).hom.app A =
      (coinvariantsFunctor k G).map (MonoidalCategory.leftUnitor A).hom :=
  rfl

end Rep

namespace HomologicalComplex

variable (k : Type u) (G : Type v) [CommRing k] [Monoid G]

/-- Degreewise tensor-unit comparison between the coinvariant complexes of an
arbitrary chain complex of representations. -/
noncomputable def coinvariantsTensorTrivialIso
    (K : ChainComplex (Rep.{u} k G) ℕ) :
    (((Rep.coinvariantsTensor k G).obj
        (Rep.trivial k G k)).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj K ≅
      ((Rep.coinvariantsFunctor k G).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj K :=
  (NatIso.mapHomologicalComplex (Rep.coinvariantsTensorTrivialNatIso k G)
    (ComplexShape.down ℕ)).app K

/-- Each forward component of `coinvariantsTensorTrivialIso` is the
coinvariant map of the monoidal left unitor. -/
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

/-- Native group homology with trivial coefficients, computed from Mathlib's
bar resolution. This hides the classical decidable-equality choice required
by `groupHomologyIso`. -/
noncomputable def trivialBarResolutionIso (n : ℕ) :
    groupHomology (Rep.trivial k G k) n ≅
      ((Rep.barResolution k G).complex.coinvariantsTensorObj
        (Rep.trivial k G k)).homology n := by
  classical
  exact groupHomologyIso (Rep.trivial k G k) n (Rep.barResolution k G)

/-- The canonical object-level comparison from left-derived coinvariants of
the trivial representation to native group homology.

Both calculations use `Rep.barResolution k G`; the middle isomorphism is the
degreewise tensor-unit comparison `coinvariantsTensorTrivialIso`. Mathlib's bar
resolution currently requires the coefficient ring and group in the same
universe, which is the only reason for the shared universe in this signature. -/
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

/-- The forward derived-coinvariants comparison is exactly the common bar
resolution comparison, followed by the inverse tensor-unit homology map and
the inverse native group-homology comparison. -/
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
