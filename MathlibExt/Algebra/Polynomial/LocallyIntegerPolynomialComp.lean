/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.LocallyIntegerPolynomial

/-!
# Composition of locally integer polynomial functions

On the integers, the composition of two locally integer polynomial functions is again locally
integer polynomial.
-/

namespace MetaMathlibExt

/-- **$\mathrm{LIP}(\mathbb{Z})$ is closed under composition.** If $f$ and $g$ lie in
$\mathrm{LIP}(\mathbb{Z})$, the ring of locally integer polynomial functions
$\mathbb{Z} \to \mathbb{Z}$, then so does the composite $x \mapsto f(g(x))$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Theorem 5 (`integers-2025-A41-thm-5`). -/
public theorem lip_univ_comp {f g : ↥(Set.univ : Set ℤ) → ℤ}
    (hf : f ∈ lipSubring Set.univ) (hg : g ∈ lipSubring Set.univ) :
    (fun x => f ⟨g x, Set.mem_univ _⟩) ∈ lipSubring Set.univ := by
  rw [mem_lipSubring_iff]
  intro X
  let g' (x : (Set.univ : Set ℤ)) : (Set.univ : Set ℤ) := ⟨g x, Set.mem_univ _⟩
  obtain ⟨q, hq⟩ := mem_lipSubring_iff.mp hg X
  obtain ⟨p, hp⟩ := mem_lipSubring_iff.mp hf (X.image g')
  refine ⟨p.comp q, ?_⟩
  intro x hx
  rw [Polynomial.eval_comp, hq x hx]
  exact hp (g' x) (Finset.mem_image_of_mem g' hx)

end MetaMathlibExt
