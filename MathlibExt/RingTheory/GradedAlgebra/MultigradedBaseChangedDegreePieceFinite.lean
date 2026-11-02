/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.GradedAlgebra.MultigradedBetti
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Finiteness.Basic

@[expose] public section

namespace MetaMathlibExt

universe u

/--
**Finite bases give finite-dimensional multidegree pieces.** Let $K$ be a field, let
$R = K[x_1, \dots, x_n]$, let $M$ be a multigraded polynomial module over $R$, and let $F$ be a
multigraded free resolution of $M$ whose term $F_i$ has the homogeneous basis
$(e_j)_{j \in \iota_i}$. Write $K \otimes_R F$ for the chain complex of $K$-vector spaces obtained
from $F$ by extending scalars along the evaluation $R \to K$ at $x = 0$. If $\iota_i$ is finite,
then for every $\alpha \in \mathbb{Z}^n$ the degree-$\alpha$ piece of $(K \otimes_R F)_i$, the
$K$-span of the vectors $1 \otimes e_j$ with $e_j$ of degree $\alpha$, is finite-dimensional
over $K$.

Proves `Wanted` entry `MultigradedFreeResolution.baseChangedDegreePiece_finite`.

Source: Benjamin Braun and
Brian Davis, "Antichain Simplices," Journal of Integer Sequences 23 (2020),
lines 862–867, `https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`.
-/
theorem MultigradedFreeResolution.baseChangedDegreePiece_finite
    (K : Type u) [Field K] (n : Nat) (M : Type u) [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (targetGraded : MultigradedPolynomialModule K n M)
    (resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M))
    (ι : Nat → Type u)
    (res : MultigradedFreeResolution K n M targetGraded resolution ι)
    (α : Fin n →₀ Int) (i : Nat) [Finite (ι i)] :
    Module.Finite K ↥(baseChangedDegreePiece (K := K) (n := n) (M := M)
      targetGraded resolution ι res i α) := by
  let : Module K ↥(resolution.complex.X i) :=
    Module.compHom _ (MvPolynomial.C : K →+* MvPolynomial (Fin n) K)
  let : Algebra (MvPolynomial (Fin n) K) K := zeroEval.toAlgebra
  have hfin : { y : ↥((baseChangedComplex resolution).X i) |
      ∃ j : ι i, (res.termFree i).degree j = α ∧
        y = (res.termFree i).basis.baseChange K j }.Finite := by
    apply Set.Finite.subset
      (Set.finite_range (fun j : ι i => (res.termFree i).basis.baseChange K j))
    intro y hy
    obtain ⟨j, _, rfl⟩ := hy
    exact Set.mem_range_self j
  have h := Module.Finite.span_of_finite K hfin
  rwa [show baseChangedDegreePiece (K := K) (n := n) (M := M)
      targetGraded resolution ι res i α =
      Submodule.span K { y : ↥((baseChangedComplex resolution).X i) |
        ∃ j : ι i, (res.termFree i).degree j = α ∧
          y = (res.termFree i).basis.baseChange K j } from rfl]

end MetaMathlibExt
