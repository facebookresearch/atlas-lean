/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.Topology.Algebra.Group.Units

/-!
# Ideles of a number field

This file defines ideles with their standard topology. The finite ideles are a restricted product
of the groups `K_vˣ` with respect to the integral unit subgroups `O_vˣ`. This is not the topology
that the units of the adele ring inherit as a subspace.

The full idele group is the product of the groups at infinite places and the finite ideles. We also
define the diagonal principal-idèle embedding and the idele class group, and record the algebraic
equivalence with the units of the adele ring.

The canonical number-field specialization uses `R = 𝓞 K`. As with `NumberField.AdeleRing`, the
definitions are stated for a Dedekind domain `R` with fraction field `K`, allowing convenient
specializations such as `R = ℤ` and `K = ℚ`. They do not model global function-field ideles.

## References

* arXiv:2607.28465v3, *Deformation of the absolute Galois groups of number fields*, line 246
* arXiv:2608.04982v1, *Weyl Subconvexity for GL₂ with Simple Supercuspidal Ramification*,
  lines 612--614
* arXiv:2608.23886v1, *Fourier Spectral Reciprocity and Canonical Hecke L-Functions*,
  lines 201--202
-/

@[expose] public section

noncomputable section

open scoped RestrictedProduct NumberField.AdeleRing

namespace NumberField

open InfinitePlace AbsoluteValue.Completion InfinitePlace.Completion IsDedekindDomain

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- **Local integral unit subgroup.** Let $R$ be a Dedekind domain with fraction field $K$, let $v$
be a height-one prime of $R$, and let $\mathcal{O}_v$ be the ring of integers of the $v$-adic
completion $K_v$ of $K$. The local integral unit subgroup is the subgroup $\mathcal{O}_v^\times$
of $K_v^\times$, consisting of the units $u$ of $K_v$ with $u \in \mathcal{O}_v$ and
$u^{-1} \in \mathcal{O}_v$. -/
abbrev localIntegralUnitSubgroup (v : HeightOneSpectrum R) :
    Subgroup ((v.adicCompletion K)ˣ) :=
  (Submonoid.ofClass (v.adicCompletionIntegers K)).units

@[simp]
theorem mem_localIntegralUnitSubgroup {v : HeightOneSpectrum R} {u : (v.adicCompletion K)ˣ} :
    u ∈ localIntegralUnitSubgroup R K v ↔
      (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K ∧
        ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈
          v.adicCompletionIntegers K :=
  Iff.rfl

/-- **Finite idele group.** Let $R$ be a Dedekind domain with fraction field $K$. For each
height-one prime $v$ of $R$, let $K_v$ be the $v$-adic completion of $K$ and $\mathcal{O}_v$ its
ring of integers. The finite idele group is the restricted product of the unit groups $K_v^\times$
over all height-one primes $v$ of $R$ with respect to the subgroups $\mathcal{O}_v^\times$: the
families $(x_v)_v$ with $x_v \in K_v^\times$ for every $v$ and $x_v \in \mathcal{O}_v^\times$ for
all but finitely many $v$, with componentwise multiplication and the restricted-product topology. -/
def FiniteIdeleGroup :=
  Πʳ v : HeightOneSpectrum R,
    [(v.adicCompletion K)ˣ, localIntegralUnitSubgroup R K v]

namespace FiniteIdeleGroup

instance : CommGroup (FiniteIdeleGroup R K) := inferInstanceAs <|
  CommGroup <| Πʳ v : HeightOneSpectrum R,
    [(v.adicCompletion K)ˣ, localIntegralUnitSubgroup R K v]

instance : TopologicalSpace (FiniteIdeleGroup R K) := inferInstanceAs <|
  TopologicalSpace <| Πʳ v : HeightOneSpectrum R,
    [(v.adicCompletion K)ˣ, localIntegralUnitSubgroup R K v]

instance : DFunLike (FiniteIdeleGroup R K) (HeightOneSpectrum R)
    (fun v ↦ (v.adicCompletion K)ˣ) where
  coe a := a.1
  coe_injective _ _ := Subtype.ext

/-- **The local integral units are open.** Let $R$ be a Dedekind domain with fraction field $K$,
let $v$ be a height-one prime of $R$, and let $\mathcal{O}_v$ be the ring of integers of the
$v$-adic completion $K_v$ of $K$. Then $\mathcal{O}_v^\times$ is an open subset of the unit group
$K_v^\times$. -/
theorem isOpen_localIntegralUnitSubgroup (v : HeightOneSpectrum R) :
    IsOpen (localIntegralUnitSubgroup R K v : Set ((v.adicCompletion K)ˣ)) := by
  let O := v.adicCompletionIntegers K
  have hO : IsOpen (O : Set (v.adicCompletion K)) := Valued.isOpen_valuationSubring _
  rw [show (localIntegralUnitSubgroup R K v : Set ((v.adicCompletion K)ˣ)) =
      Units.val ⁻¹' (O : Set (v.adicCompletion K)) ∩
        (fun x : (v.adicCompletion K)ˣ ↦
          ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)) ⁻¹'
            (O : Set (v.adicCompletion K)) by
    ext x
    rfl]
  exact (hO.preimage Units.continuous_val).inter
    (hO.preimage (Units.continuous_val.comp continuous_inv))

instance : IsTopologicalGroup (FiniteIdeleGroup R K) :=
  haveI : Fact (∀ v : HeightOneSpectrum R,
      IsOpen (localIntegralUnitSubgroup R K v : Set ((v.adicCompletion K)ˣ))) :=
    ⟨isOpen_localIntegralUnitSubgroup R K⟩
  RestrictedProduct.isTopologicalGroup
    (fun v : HeightOneSpectrum R ↦ (v.adicCompletion K)ˣ)

end FiniteIdeleGroup

/-- **Infinite idele group.** For a field $K$, the infinite idele group is the product
$\prod_v K_v^\times$ of the unit groups of the completions $K_v$ of $K$ over all infinite places
$v$ of $K$, with componentwise multiplication and the product topology. -/
def InfiniteIdeleGroup := (v : InfinitePlace K) → (v.Completion)ˣ

namespace InfiniteIdeleGroup

instance : CommGroup (InfiniteIdeleGroup K) := inferInstanceAs <|
  CommGroup <| (v : InfinitePlace K) → (v.Completion)ˣ

instance : TopologicalSpace (InfiniteIdeleGroup K) := inferInstanceAs <|
  TopologicalSpace <| (v : InfinitePlace K) → (v.Completion)ˣ

instance : IsTopologicalGroup (InfiniteIdeleGroup K) := inferInstanceAs <|
  IsTopologicalGroup <| (v : InfinitePlace K) → (v.Completion)ˣ

end InfiniteIdeleGroup

-- Upstream `NumberField.IdeleGroup` (`𝔸[R, K]ˣ`) and
-- `NumberField.IdeleClassGroup` are reused unshadowed. The restricted-product
-- model below uses the explicit `TopologicalIdeleGroup` type to preserve the local
-- topology; see `TopologicalIdeleGroup.unitsEquiv` for the algebraic bridge.

/-- **Topological idele group.** Let $R$ be a Dedekind domain with fraction field $K$. The
topological idele group is the product $\mathbb{I}_{K,\infty} \times \mathbb{I}_{K,f}$ of the
infinite idele group $\mathbb{I}_{K,\infty} = \prod_w K_w^\times$, the product of the unit groups
of the completions of $K$ at its infinite places $w$, and the finite idele group
$\mathbb{I}_{K,f}$, the restricted product of the unit groups $K_v^\times$ of the completions at
the height-one primes $v$ of $R$ with respect to the integral unit groups $\mathcal{O}_v^\times$.
It carries the componentwise group structure and the product of the product topology on
$\mathbb{I}_{K,\infty}$ and the restricted-product topology on $\mathbb{I}_{K,f}$.

As a group it is isomorphic to the unit group of the adele ring of $K$, but its topology differs
from the subspace topology on those units. -/
def TopologicalIdeleGroup :=
  (InfiniteIdeleGroup K × FiniteIdeleGroup R K)

namespace TopologicalIdeleGroup

instance : CommGroup (TopologicalIdeleGroup R K) := inferInstanceAs <|
  CommGroup (InfiniteIdeleGroup K × FiniteIdeleGroup R K)

instance : TopologicalSpace (TopologicalIdeleGroup R K) := inferInstanceAs <|
  TopologicalSpace (InfiniteIdeleGroup K × FiniteIdeleGroup R K)

instance : IsTopologicalGroup (TopologicalIdeleGroup R K) := inferInstanceAs <|
  IsTopologicalGroup (InfiniteIdeleGroup K × FiniteIdeleGroup R K)

/-- **Diagonal map into the infinite ideles.** For a field $K$, this is the group homomorphism
from $K^\times$ to the infinite idele group of $K$ that sends $x$ to the family of its images in the
completions $K_v$ of $K$, one for each infinite place $v$ of $K$. -/
def infinitePrincipalEmbedding : Kˣ →* InfiniteIdeleGroup K :=
  MulEquiv.piUnits.toMonoidHom.comp <|
    Units.map (algebraMap K (InfiniteAdeleRing K)).toMonoidHom

/-- **Diagonal map into the finite ideles.** Let $R$ be a Dedekind domain with fraction field $K$.
This is the group homomorphism from $K^\times$ to the finite idele group of $R$ and $K$ that sends
$x$ to the family of its images in the $v$-adic completions $K_v$ of $K$, one for each height-one
prime $v$ of $R$. -/
def finitePrincipalEmbedding : Kˣ →* FiniteIdeleGroup R K :=
  (RestrictedProduct.unitsEquiv
    (fun v : HeightOneSpectrum R ↦ v.adicCompletion K)).toMonoidHom.comp <|
      FiniteAdeleRing.unitEmbedding R K

/-- **Diagonal map into the ideles.** Let $R$ be a Dedekind domain with fraction field $K$. This
is the group homomorphism from $K^\times$ to the topological idele group of $R$ and $K$ whose
infinite component sends $x$ to its images in the completions of $K$ at all infinite places of
$K$, and whose finite component sends $x$ to its images in the $v$-adic completions $K_v$ of $K$
at all height-one primes $v$ of $R$. -/
def principalEmbedding : Kˣ →* TopologicalIdeleGroup R K :=
  (infinitePrincipalEmbedding K).prod (finitePrincipalEmbedding R K)

@[simp]
theorem infinitePrincipalEmbedding_apply (x : Kˣ) (v : InfinitePlace K) :
    infinitePrincipalEmbedding K x v =
      Units.map (algebraMap K v.Completion).toMonoidHom x :=
  rfl

@[simp]
theorem finitePrincipalEmbedding_apply (x : Kˣ) (v : HeightOneSpectrum R) :
    finitePrincipalEmbedding R K x v =
      Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x :=
  rfl

@[simp]
theorem principalEmbedding_fst (x : Kˣ) :
    (principalEmbedding R K x).1 = infinitePrincipalEmbedding K x :=
  rfl

@[simp]
theorem principalEmbedding_snd (x : Kˣ) :
    (principalEmbedding R K x).2 = finitePrincipalEmbedding R K x :=
  rfl

/-- **Principal ideles.** Let $R$ be a Dedekind domain with fraction field $K$. The subgroup of
principal ideles is the image of the diagonal homomorphism from $K^\times$ to the topological idele
group of $R$ and $K$, which sends $x$ to its images in the completions of $K$ at all infinite
places of $K$ and at all height-one primes of $R$. -/
def principalIdeles : Subgroup (TopologicalIdeleGroup R K) :=
  (principalEmbedding R K).range

/-- **Ideles as units of the adele ring.** Let $R$ be a Dedekind domain with fraction field $K$,
and let $\mathbb{A}_K$ be the adele ring of $K$ built from the infinite places of $K$ and the
height-one primes of $R$. For an infinite place $w$ of $K$ write $K_w$ for the completion of $K$
at $w$, and for a height-one prime $v$ of $R$ write $K_v$ for the $v$-adic completion of $K$.
This is the group isomorphism from the unit group $\mathbb{A}_K^\times$ to the topological idele
group that sends a unit adele $a$ to the idele whose component at each infinite place $w$ is the
component $a_w \in K_w^\times$ of $a$ and whose component at each height-one prime $v$ is the
component $a_v \in K_v^\times$ of $a$.

It is stated only as an isomorphism of groups: the topological idele group carries the
restricted-product topology, not the topology induced on the units of the adele ring. -/
def unitsEquiv :
    (AdeleRing R K)ˣ ≃* TopologicalIdeleGroup R K :=
  MulEquiv.prodUnits.trans <| MulEquiv.prodCongr MulEquiv.piUnits <|
    RestrictedProduct.unitsEquiv (fun v : HeightOneSpectrum R ↦ v.adicCompletion K)

@[simp]
theorem unitsEquiv_globalUnit (x : Kˣ) :
    unitsEquiv R K (Units.map (algebraMap K (AdeleRing R K)).toMonoidHom x) =
      principalEmbedding R K x :=
  rfl

/-- **The diagonal map into the ideles is injective.** Let $K$ be a number field and let $R$ be a
Dedekind domain with fraction field $K$. The diagonal homomorphism from $K^\times$ to the
topological idele group of $R$ and $K$, which sends $x$ to its images in the completions of $K$ at
all infinite places of $K$ and at all height-one primes of $R$, is injective. -/
theorem principalEmbedding_injective [NumberField K] :
    Function.Injective (principalEmbedding R K) := by
  intro x y hxy
  have hmap :
      unitsEquiv R K (Units.map (algebraMap K (AdeleRing R K)).toMonoidHom x) =
        unitsEquiv R K (Units.map (algebraMap K (AdeleRing R K)).toMonoidHom y) := by
    simpa only [unitsEquiv_globalUnit] using hxy
  exact Units.map_injective (AdeleRing.algebraMap_injective R K) <|
    (unitsEquiv R K).injective hmap

end TopologicalIdeleGroup

/-- **Topological idele class group.** Let $R$ be a Dedekind domain with fraction field $K$. The
topological idele class group is the quotient group of the topological idele group of $R$ and $K$
by its subgroup of principal ideles, the image of the diagonal homomorphism from $K^\times$. -/
abbrev TopologicalIdeleClassGroup :=
  (TopologicalIdeleGroup R K) ⧸ (TopologicalIdeleGroup.principalIdeles R K)

end NumberField
