/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:

`TauCeti/GroupTheory/TransversalWord.lean`
(TauCeti, revision `62bbc0596dc3539d488232e4e924a338548ea0a9`):
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Claude.

`TauCeti/RepresentationTheory/Homological/ContCohomology/Corestriction/Basic.lean`
(TauCeti, revision `62bbc0596dc3539d488232e4e924a338548ea0a9`):
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Tau Ceti contributors.

Modifications: the left-coset transversal formula is kept, and the field corestriction is
specified by its values on actual two-cocycle classes; no abstract transfer or evaluation map
is assumed.
-/
module

public import MathlibExt.AlgebraicGeometry.BrauerInteroperability
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-!
# Native field corestriction normalized on two-cocycles

The subgroup fixes the image of a given finite extension in the actual
separable closure. The field and Galois dictionaries below contain only actual
embeddings/equivalences and their coefficient normalization. A corestriction
provider must satisfy the full Tau transversal formula on every cocycle class.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.BrauerCorestriction

open CategoryTheory BrauerCoefficients BrauerInteroperability
open scoped BigOperators Pointwise

section Words

variable {G : Type*} [Group G] (U : Subgroup G) (t : G ⧸ U → G)

/-- Tau's left-transversal word, with the inverse-translated coset index. -/
def transversalWord (u : G ⧸ U) (g : G) : G :=
  (t u)⁻¹ * g * t (g⁻¹ • u)

/-- A genuine left transversal gives subgroup-valued words. -/
theorem transversalWord_mem
    (ht : ∀ u : G ⧸ U, (QuotientGroup.mk (t u) : G ⧸ U) = u)
    (u : G ⧸ U) (g : G) : transversalWord U t u g ∈ U := by
  have h : (QuotientGroup.mk (g * t (g⁻¹ • u)) : G ⧸ U) =
      QuotientGroup.mk (t u) := by
    rw [← smul_eq_mul, ← MulAction.Quotient.smul_mk, ht, smul_inv_smul, ht]
  rw [transversalWord, mul_assoc, ← QuotientGroup.eq, h]

/-- The translated index is forced by the word cocycle identity. -/
theorem transversalWord_mul (u : G ⧸ U) (g h : G) :
    transversalWord U t u g * transversalWord U t (g⁻¹ • u) h =
      transversalWord U t u (g * h) := by
  simp only [transversalWord, mul_inv_rev, mul_smul]
  group

end Words

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (σ : L →ₐ[K] SeparableClosure K)

/-- The actual subgroup of absolute automorphisms fixing the extension image. -/
def fixingSubgroup : Subgroup (Field.absoluteGaloisGroup K) :=
  ((separableClosure K (AlgebraicClosure K)).val.comp σ).fieldRange.fixingSubgroup

/-- Galois data of a field extension $L/K$ with a $K$-embedding $\sigma : L \to K^{\mathrm{sep}}$:
a ring isomorphism $L^{\mathrm{sep}} \cong K^{\mathrm{sep}}$ of separable closures extending
$\sigma$; an isomorphism of topological groups from the absolute Galois group of $L$ to the
subgroup of the absolute Galois group of $K$ fixing $\sigma(L)$ (`fixingSubgroup`), for which the
ring isomorphism is equivariant; and the facts that this subgroup has finite index and is open. -/
structure FiniteFieldPair where
  closure : SeparableClosure L ≃+* SeparableClosure K
  closure_base : ∀ a : L, closure (algebraMap L (SeparableClosure L) a) = σ a
  galois : Field.absoluteGaloisGroup L ≃ₜ* fixingSubgroup K L σ
  equivariant : ∀ (g : Field.absoluteGaloisGroup L) (u : SeparableClosure L),
    closure (g.separableClosure u) = (galois g).val.separableClosure (closure u)
  finite_cosets : Finite ((Field.absoluteGaloisGroup K) ⧸ fixingSubgroup K L σ)
  open_subgroup : IsOpen (fixingSubgroup K L σ : Set (Field.absoluteGaloisGroup K))

/-- The actual unit transport for the finite-field dictionary. -/
def transportUnits (P : FiniteFieldPair K L σ) : SepUnits L ≃+ SepUnits K :=
  (Units.mapEquiv P.closure.toMulEquiv).toAdditive

/-- The full inhomogeneous corestriction formula of Tau, on an actual cocycle.
The second word is indexed by `g⁻¹ • u`; omitting it changes the operation. -/
def transferValue (P : FiniteFieldPair K L σ)
    (t : (Field.absoluteGaloisGroup K) ⧸ fixingSubgroup K L σ →
      Field.absoluteGaloisGroup K)
    (ht : ∀ u, (QuotientGroup.mk (t u) :
      (Field.absoluteGaloisGroup K) ⧸ fixingSubgroup K L σ) = u)
    (c : TwoCocycles L) (g h : Field.absoluteGaloisGroup K) : SepUnits K := by
  letI := P.finite_cosets
  letI := Fintype.ofFinite ((Field.absoluteGaloisGroup K) ⧸ fixingSubgroup K L σ)
  exact ∑ u, unitAction K (t u) (transportUnits K L σ P
    (inhomogeneousValue L c
      (P.galois.symm ⟨transversalWord (fixingSubgroup K L σ) t u g,
        transversalWord_mem _ _ ht u g⟩)
      (P.galois.symm ⟨transversalWord (fixingSubgroup K L σ) t (g⁻¹ • u) h,
        transversalWord_mem _ _ ht (g⁻¹ • u) h⟩)))

/-- Corestriction maps $\mathrm{Br}(L) \to \mathrm{Br}(K)$ for the extension $L/K$ with the
embedding $\sigma : L \to K^{\mathrm{sep}}$ and the Galois data `P`, where
$\mathrm{Br}(K) = H^2(G_K, (K^{\mathrm{sep}})^\times)$ for the absolute Galois group $G_K$, given
on cocycles by the transfer formula: additive maps $\mathrm{cor}$ such that, for every left
transversal $t$ of the subgroup of $G_K$ fixing $\sigma(L)$ and every continuous two-cocycle $c$
of $G_L$ with values in $(L^{\mathrm{sep}})^\times$, there is a two-cocycle $d$ of $G_K$ whose
inhomogeneous values are those of the transfer of $c$ along $t$ (`transferValue`) and
$\mathrm{cor}$ sends the class of $c$ to the class of $d$. -/
abbrev NormalizedCorestriction (P : FiniteFieldPair K L σ) :=
  {cor : Br L →+ Br K //
    ∀ (t : (Field.absoluteGaloisGroup K) ⧸ fixingSubgroup K L σ →
        Field.absoluteGaloisGroup K)
      (ht : ∀ u, (QuotientGroup.mk (t u) :
        (Field.absoluteGaloisGroup K) ⧸ fixingSubgroup K L σ) = u)
      (c : TwoCocycles L),
      ∃ d : TwoCocycles K,
        (∀ g h, inhomogeneousValue K d g h = transferValue K L σ P t ht c g h) ∧
          cor (cocycleClass L c) = cocycleClass K d}

end AlgebraicGeometry.BrauerCorestriction
