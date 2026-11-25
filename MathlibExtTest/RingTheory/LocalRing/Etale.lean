/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.LocalRing.Etale
public import Mathlib.RingTheory.DedekindDomain.Basic

import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

@[expose] public section

open Polynomial

public theorem test_formallyUnramified_of_isUnit_aeval_derivative_adjoin_eq_top
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (x : S) (P : R[X])
    (h0 : aeval x P = 0) (hu : IsUnit (aeval x P.derivative))
    (htop : Algebra.adjoin R ({x} : Set S) = ⊤) : Algebra.FormallyUnramified R S :=
  Algebra.FormallyUnramified.of_isUnit_aeval_derivative_of_adjoin_eq_top x P h0 hu htop

public theorem test_etale_forward_exists_adjoin_eq_top_separable_minpoly {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [IsLocalRing S]
    [Module.Finite R S] [FaithfulSMul R S] [Module.Flat R S]
    [Algebra.FinitePresentation R S] (h : Algebra.Etale R S) :
    ∃ x : S, Algebra.adjoin R ({x} : Set S) = ⊤ ∧
      ((minpoly R x).map (IsLocalRing.residue R)).Separable :=
  (Algebra.etale_iff_exists_adjoin_eq_top_and_separable_map_minpoly).mp h

public theorem test_etale_reverse_exists_adjoin_eq_top_separable_minpoly {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [IsLocalRing S]
    [Module.Finite R S] [FaithfulSMul R S] [Module.Flat R S]
    [Algebra.FinitePresentation R S]
    (h : ∃ x : S, Algebra.adjoin R ({x} : Set S) = ⊤ ∧
      ((minpoly R x).map (IsLocalRing.residue R)).Separable) :
    Algebra.Etale R S :=
  (Algebra.etale_iff_exists_adjoin_eq_top_and_separable_map_minpoly).mpr h

public theorem test_etale_iff_dedekind_finite_torsionFree {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [IsLocalRing S]
    [IsDedekindDomain R] [Module.Finite R S] [FaithfulSMul R S]
    [Module.IsTorsionFree R S] :
    Algebra.Etale R S ↔
      ∃ x : S, Algebra.adjoin R ({x} : Set S) = ⊤ ∧
        ((minpoly R x).map (IsLocalRing.residue R)).Separable := by
  let _ : Module.Flat R S := inferInstance
  let _ : Module.FinitePresentation R S := Module.finitePresentation_of_finite R S
  let _ : Algebra.FinitePresentation R S :=
    Algebra.FinitePresentation.of_finitePresentation R S
  exact Algebra.etale_iff_exists_adjoin_eq_top_and_separable_map_minpoly

end
