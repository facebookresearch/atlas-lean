/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import MathlibExt.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Flat extension of scalars preserves homology across universes

Flat extension of scalars preserves homology of short complexes.
The ring universes are independent, and module carriers use a common
universe. Subsequent scalar restriction along an arbitrary map also
preserves homology; that second map need not be flat.

The same-universe source theorem was originally formalized in
`FormalizedTextbooks/Hartshorne1977/Algebra/Category/ModuleCat/FlatHomology.lean`,
whose original header records `Authors: Muse` and copyright by Muse.
That original formalization credit is preserved here; this generalized
canonical API and the compatible source delegation are authored by @toskua.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
universe u v w x
namespace ModuleCat

/-- Flat scalar extension preserves actual homology, with independent ring
universes and the original common module carrier universe. -/
theorem preservesHomology_extendScalars_of_flat
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) :
    (extendScalars.{u,v,max u v w} f).PreservesHomology := by
  let : Algebra R S := f.toAlgebra
  let : Module.Flat R S := (RingHom.flat_algebraMap_iff).mp hf
  apply Functor.preservesHomology_of_map_exact
  intro C hC
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hC ⊢
  change Function.Exact (C.f.hom.lTensor S) (C.g.hom.lTensor S)
  exact Module.Flat.lTensor_exact S hC

/-- Flat extension followed by actual scalar restriction preserves homology across universes. -/
theorem preservesHomology_extendScalars_restrictScalars_of_flat
    {R : Type u} {S : Type v} {Q : Type w} [CommRing R] [CommRing S] [CommRing Q]
    (f : R →+* Q) (g : S →+* Q) (hf : f.Flat) :
    (extendScalars.{u, w, max u v w x} f ⋙
      restrictScalars.{max u v w x, v, w} g).PreservesHomology := by
  let E := extendScalars.{u, w, max u v w x} f
  have : E.PreservesHomology := preservesHomology_extendScalars_of_flat.{u, w, max v x} f hf
  apply Functor.preservesHomology_of_map_exact
  intro C hC
  exact restrictScalars_map_exact g (C.map E) (hC.map E)

end ModuleCat
