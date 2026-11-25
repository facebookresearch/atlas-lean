/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.NeronModels
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Néron providers over arbitrary discrete valuation rings

All generic and special fibres, extension operators, Hom maps and integral
point reduction are actual completed MathlibExt constructions. These
requests supply only the remaining geometric model/group/mapping-property
providers. The base may be ramified or equal characteristic; completeness
and a fixed prime field are not required.

Conrad, *Néron models, Tamagawa factors, and Tate-Shafarevich groups*,
Theorem 1.1 and Remark 1.3 pp. 2–3 state finite-type existence over every
Dedekind scheme. Section 2, property 1 and Example 2.1 pp. 3–4 state the
group extension and the mapping property of an abelian scheme over the base.
https://math.stanford.edu/~conrad/BSDseminar/Notes/L3.pdf
Bosch–Lütkebohmert–Raynaud, *Néron Models*, §§1.1–1.3 and §4.4.
https://doi.org/10.1007/978-3-642-51438-8

The class permits lft Néron models used for other groups; this packet does
not claim existence for arbitrary algebraic groups or compatibility with
arbitrary ramified base change.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.NeronModelsWanted

open _root_.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry.AbelianSchemes
open MathlibExt.AlgebraicGeometry.NeronModels
open MathlibExt.AlgebraicGeometry.SemistableModels

universe u

def_wanted abelian_neron_model (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] (A : AbelianScheme (Spec (.of K))) :
    FiniteTypeNeronModel R K A.model

def_wanted neron_group_structure (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] (A : AbelianScheme (Spec (.of K)))
    (N : NeronModel R K A.model) : N.GroupStructure

theorem_wanted good_reduction_mapping_property (R : Type u) [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] (K : Type u) [Field K]
    [Algebra R K] [IsFractionRing R K] (A : AbelianScheme (trait R)) :
    HasMappingProperty R K A.model

theorem_wanted etale_base_change (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] (R' : Type u) [CommRing R'] [IsDomain R']
    [IsDiscreteValuationRing R'] (K' : Type u) [Field K'] [Algebra R' K']
    [IsFractionRing R' K'] (φ : trait R' ⟶ trait R) [Etale φ]
    (ψ : Spec (.of K') ⟶ Spec (.of K))
    (h : IsPullback ψ (genericInclusion R' K') (genericInclusion R K) φ)
    (A : AbelianScheme (Spec (.of K))) (M : NeronModel R K A.model)
    (N : NeronModel R' K' ((Over.pullback ψ).obj A.model)) :
    IsIso (baseChangeMap R K R' K' φ ψ h.w M N)

end WantedExt.AlgebraicGeometry.NeronModelsWanted
