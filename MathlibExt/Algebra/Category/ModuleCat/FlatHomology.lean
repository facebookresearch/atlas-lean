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

/-
The same-universe source theorem was originally formalized in
`FormalizedTextbooks/Hartshorne1977/Algebra/Category/ModuleCat/FlatHomology.lean`,
whose original header records `Authors: Muse` and copyright by Muse.
That original formalization credit is preserved here; this generalized
canonical API and the compatible source delegation are authored by @toskua.
-/

/-!
# Flat scalar extension preserves homology across ring worlds

Let f:R→S be a flat homomorphism of commutative rings in independent
worlds u,v. Extension of scalars preserves homology of short complexes
for modules at the common height Γ=max(u,v,w).

More generally, for f:R→Q flat and an arbitrary commutative-ring
map g:S→Q, extension along f followed by restriction along g
preserves homology at height max(u,v,w,x).
Only f is required to be flat; scalar restriction is exact for
every g.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
universe u v w x
namespace ModuleCat

/-- For commutative rings R,S in independent worlds and
a flat map f:R→S, extension of scalars preserves homology.
The source module carrier height is Γ=max(u,v,w), so the
extension and homology objects use that common height. -/
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

/-- For commutative-ring maps f:R→Q,g:S→Q, assume f flat.
Extension along f followed by restriction along g preserves
homology of short complexes at height max(u,v,w,x).
No flatness of g is required. -/
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
