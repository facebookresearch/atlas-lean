/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.CategoryTheory.TensorGeneratedMonodromy

@[expose] public noncomputable section

/-!
# The actual tensor-generated fibre group and affine monodromy

Authors: Pierre Deligne, James S. Milne.
Source: Tannakian Categories, Theorem 2.11, Proposition 2.20 and
Corollary 2.9, https://www.jmilne.org/math/xnotes/tc.pdf.

The category, its faithful monoidal fibre, coefficient extension, tensor
automorphism group, generator evaluation and determinant-inverted affine
model are actual objects with fixed maps. Generic finite-group Tannaka is
already Mathlib; this request is the general tensor-generated affine
comparison over every coefficient algebra. It does not assume that the
image is the full general linear group or a paper's predicted monodromy group.
-/

namespace WantedExt.CategoryTheory.TensorGeneratedMonodromy

open _root_.CategoryTheory
open MathlibExt.CategoryTheory.TensorGeneratedMonodromy

universe u v

/-- Generator evaluation identifies actual tensor automorphisms with the
coefficient-algebra points of the actual image closure inside GL_r. -/
public theorem_wanted tensorAutomorphism_generator_image
    (k : Type u) [Field k] (Γ : Type v) [Group Γ] (r : ℕ)
    (ρ : Γ →* Matrix.GeneralLinearGroup (Fin r) k)
    (S : Type u) [CommRing S] [Algebra k S] :
    Function.Injective (generatorMatrix k Γ r ρ S) ∧
      ∀ g : Matrix.GeneralLinearGroup (Fin r) S,
        (∃ η : TensorAutomorphisms k Γ r ρ S, generatorMatrix k Γ r ρ S η = g) ↔
          IsMonodromyPoint k Γ r ρ S g

end WantedExt.CategoryTheory.TensorGeneratedMonodromy
