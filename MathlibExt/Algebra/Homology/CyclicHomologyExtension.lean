/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-
Modifications copyright (c) 2026 Meta Platforms, Inc. and affiliates.
-/
/-
Ported from TauCetiProject/TauCeti at
62bbc0596dc3539d488232e4e924a338548ea0a9:
TauCeti/Algebra/Homology/ModuleCat/Extend.lean
Public source: https://github.com/TauCetiProject/TauCeti
The original contributors' copyright, author and Apache License 2.0
notice is retained above. Modification notice: use the explicitly
listed MathlibExt ports for this complete SBI dependency closure;
retain the mathematical declarations and original names. Identity-scalar
multilinear maps and endomorphism-application lemmas use the pinned
Mathlib API; the finite-coordinate port keeps only its four needed lemmas.
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import MathlibExt.Algebra.Homology.CyclicModuleHomology

/-!
# Homology classes of an extended complex of modules

Mathlib identifies the homology of a complex `K` in degree `j` with the homology of its extension
`K.extend e` along an embedding `e` of complex shapes in degree `e.f j`
(`HomologicalComplex.extendHomologyIso`). For complexes of modules, this file describes the
inverse of that identification on classes of cycles: it sends the class of a cycle `x` of `K` to
the class of `x`, regarded as an element of `K.extend e` through `HomologicalComplex.extendXIso`.

## Main results

* `HomologicalComplex.extendHomologyIso_inv_homologyπ_moduleCatCyclesMk`: the class of a cycle is
  sent to the class of the same element of the extended complex.
-/

public section

open CategoryTheory

namespace HomologicalComplex

variable {R : Type*} [Ring R] {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (K : HomologicalComplex (ModuleCat R) c) (e : c.Embedding c')

/-- The identification of the homology of a complex of modules with that of its extension sends
the class of a cycle `x` to the class of `x`, regarded as an element of the extended complex. -/
lemma extendHomologyIso_inv_homologyπ_moduleCatCyclesMk {j : ι} {j' : ι'} (hj' : e.f j = j')
    (x : K.X j) (k : ι) (hk : c.next j = k) (hx : K.d j k x = 0) (k' : ι')
    (hk' : c'.next j' = k') (hx' : (K.extend e).d j' k' ((K.extendXIso e hj').inv x) = 0) :
    (K.extendHomologyIso e hj').inv ((K.homologyπ j) (K.moduleCatCyclesMk x k hk hx)) =
      ((K.extend e).homologyπ j') ((K.extend e).moduleCatCyclesMk _ k' hk' hx') := by
  rw [← ModuleCat.comp_apply, homologyπ_extendHomologyIso_inv, ModuleCat.comp_apply]
  congr 1
  apply moduleCat_iCycles_injective
  rw [← ModuleCat.comp_apply, extendCyclesIso_inv_iCycles, ModuleCat.comp_apply,
    iCycles_moduleCatCyclesMk, iCycles_moduleCatCyclesMk]

end HomologicalComplex
