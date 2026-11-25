/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.AsymptoticMorphism.IteratedSplitPullback
public import MathlibExt.Analysis.CStarAlgebra.ContinuousMap.IntervalGluing

/-!
# Matching interval paths after finite asymptotic iteration

For a nonunital complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient
C-star norm, and define α⁰X=X, αⁿ⁺¹X=α(αⁿX). For B a nonunital complex C-star algebra and n∈ℕ,
let P_B=C([0,1],B), e_s=αⁿ(ev_s):αⁿP_B→αⁿB, and M_n(B)={(x,y)∈αⁿP_B×αⁿP_B:e_1(x)=e_0(y)} with
its closed-subalgebra maximum norm. The algebra αⁿ(MatchingPaths B) is star-isomorphic to
M_n(B). The gluing map M_n(B)→αⁿP_B comes from the finite iterate of midpoint path gluing,
with initial endpoint e_0 of the first coordinate and final endpoint e_1 of the second.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace AsymptoticAlgebra

universe uB uX uY uZ

attribute [local instance] cStarAlgebra

/-- **Evaluation on a finite iterate of the path algebra.**

For a nonunital complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient
C-star norm, and define α⁰X=X, αⁿ⁺¹X=α(αⁿX). For a nonunital complex C-star algebra B, n∈ℕ and
s∈[0,1], endpointHom n s B:αⁿ(C([0,1],B))→αⁿB is αⁿ(ev_s), the finite iterate of path
evaluation.
-/
@[no_expose]
def endpointHom (n : ℕ) (t : unitInterval)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    IteratedAsymptoticAlgebra n C(unitInterval, B) →⋆ₙₐ[ℂ]
      IteratedAsymptoticAlgebra n B :=
  IteratedAsymptoticAlgebra.map n
    (ContinuousMap.IntervalGluing.evalAt B t)

/-- **Endpoint map equals iterated evaluation.**

For a nonunital complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient
C-star norm, and define α⁰X=X, αⁿ⁺¹X=α(αⁿX). For B a nonunital complex C-star algebra, n∈ℕ and
s∈[0,1], endpointHom n s B=IteratedAsymptoticAlgebra.map n
(ContinuousMap.IntervalGluing.evalAt B s).
-/
theorem endpointHom_eq (n : ℕ) (t : unitInterval)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    endpointHom n t B =
      IteratedAsymptoticAlgebra.map n
        (ContinuousMap.IntervalGluing.evalAt B t) := by
  rfl

/-- **Pullback of finite-stage path endpoints.**

For a nonunital complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient
C-star norm, and define α⁰X=X, αⁿ⁺¹X=α(αⁿX). For B a nonunital complex C-star algebra and n∈ℕ,
let P_B=C([0,1],B), e_s=αⁿ(ev_s):αⁿP_B→αⁿB, and M_n(B)={(x,y)∈αⁿP_B×αⁿP_B:e_1(x)=e_0(y)} with
its closed-subalgebra maximum norm. IteratedMatchingPaths n B is the pullback algebra M_n(B).
-/
abbrev IteratedMatchingPaths (n : ℕ)
    (B : Type uB) [NonUnitalCStarAlgebra B] :=
  NonUnitalCStarPullback.Pullback
    (endpointHom n 1 B) (endpointHom n 0 B)

private theorem evalAt_zero_comp_constantHom
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (ContinuousMap.IntervalGluing.evalAt B 0).comp
        (ContinuousMap.IntervalGluing.constantHom B) =
      NonUnitalStarAlgHom.id ℂ B := by
  apply NonUnitalStarAlgHom.ext
  intro b
  rfl

/-- **Star equivalence between iterated matching paths and endpoint pullback.**

For a nonunital complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient
C-star norm, and define α⁰X=X, αⁿ⁺¹X=α(αⁿX). For B a nonunital complex C-star algebra and n∈ℕ,
let P_B=C([0,1],B), e_s=αⁿ(ev_s):αⁿP_B→αⁿB, and M_n(B)={(x,y)∈αⁿP_B×αⁿP_B:e_1(x)=e_0(y)} with
its closed-subalgebra maximum norm. For MatchingPaths B={(F,G)∈P_B²:F(1)=G(0)},
iteratedMatchingPathsEquiv n B:αⁿ(MatchingPaths B)≃⋆ₐ[ℂ]M_n(B) is the coordinate equivalence
induced by the iterated path projections.
-/
@[no_expose]
noncomputable def iteratedMatchingPathsEquiv (n : ℕ)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    IteratedAsymptoticAlgebra n
        (ContinuousMap.IntervalGluing.MatchingPaths B) ≃⋆ₐ[ℂ]
      IteratedMatchingPaths n B :=
  iteratedSplitPullbackEquiv n
    (ContinuousMap.IntervalGluing.evalAt B 1)
    (ContinuousMap.IntervalGluing.evalAt B 0)
    (ContinuousMap.IntervalGluing.constantHom B)
    (evalAt_zero_comp_constantHom B)

/-- **Gluing homomorphism for finite-stage matching paths.**

For a nonunital complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient
C-star norm, and define α⁰X=X, αⁿ⁺¹X=α(αⁿX). For B a nonunital complex C-star algebra and n∈ℕ,
let P_B=C([0,1],B), e_s=αⁿ(ev_s):αⁿP_B→αⁿB, and M_n(B)={(x,y)∈αⁿP_B×αⁿP_B:e_1(x)=e_0(y)} with
its closed-subalgebra maximum norm. With E_n=iteratedMatchingPathsEquiv n B and
glue:MatchingPaths B→P_B the midpoint-concatenation homomorphism, glueHomN n B:M_n(B)→αⁿP_B is
αⁿ(glue)∘E_n⁻¹.
-/
@[no_expose]
noncomputable def glueHomN (n : ℕ)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    IteratedMatchingPaths n B →⋆ₙₐ[ℂ]
      IteratedAsymptoticAlgebra n C(unitInterval, B) :=
  (IteratedAsymptoticAlgebra.map n
    (ContinuousMap.IntervalGluing.glueHom (B := B))).comp
      (iteratedMatchingPathsEquiv n B).symm.toNonUnitalStarAlgHom

private theorem evalAt_zero_comp_glueHom
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (ContinuousMap.IntervalGluing.evalAt B 0).comp
        (ContinuousMap.IntervalGluing.glueHom (B := B)) =
      (ContinuousMap.IntervalGluing.evalAt B 0).comp
        (NonUnitalCStarPullback.fstHom
          (ContinuousMap.IntervalGluing.evalAt B 1)
          (ContinuousMap.IntervalGluing.evalAt B 0)) := by
  apply NonUnitalStarAlgHom.ext
  intro p
  change ContinuousMap.IntervalGluing.glueHom p 0 = p.1.1 0
  exact ContinuousMap.IntervalGluing.glueHom_zero p

private theorem evalAt_one_comp_glueHom
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (ContinuousMap.IntervalGluing.evalAt B 1).comp
        (ContinuousMap.IntervalGluing.glueHom (B := B)) =
      (ContinuousMap.IntervalGluing.evalAt B 1).comp
        (NonUnitalCStarPullback.sndHom
          (ContinuousMap.IntervalGluing.evalAt B 1)
          (ContinuousMap.IntervalGluing.evalAt B 0)) := by
  apply NonUnitalStarAlgHom.ext
  intro p
  change ContinuousMap.IntervalGluing.glueHom p 1 = p.1.2 1
  exact ContinuousMap.IntervalGluing.glueHom_one p

private theorem comp_symm_eq_of_comp_eq
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    [NonUnitalCStarAlgebra X] [NonUnitalCStarAlgebra Y]
    [NonUnitalCStarAlgebra Z]
    (e : X ≃⋆ₐ[ℂ] Y) (p : Y →⋆ₙₐ[ℂ] Z) (q : X →⋆ₙₐ[ℂ] Z)
    (h : p.comp e.toNonUnitalStarAlgHom = q) :
    q.comp e.symm.toNonUnitalStarAlgHom = p := by
  apply NonUnitalStarAlgHom.ext
  intro y
  change q (e.symm y) = p y
  have hy := DFunLike.congr_fun h (e.symm y)
  change p (e (e.symm y)) = q (e.symm y) at hy
  exact hy.symm.trans (congrArg p (e.apply_symm_apply y))

private theorem map_fst_comp_matchingEquiv_symm (n : ℕ)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (IteratedAsymptoticAlgebra.map n
      (NonUnitalCStarPullback.fstHom
        (ContinuousMap.IntervalGluing.evalAt B 1)
        (ContinuousMap.IntervalGluing.evalAt B 0))).comp
        (iteratedMatchingPathsEquiv n B).symm.toNonUnitalStarAlgHom =
      NonUnitalCStarPullback.fstHom
        (endpointHom n 1 B) (endpointHom n 0 B) := by
  exact comp_symm_eq_of_comp_eq
    (iteratedMatchingPathsEquiv n B)
    (NonUnitalCStarPullback.fstHom
      (endpointHom n 1 B) (endpointHom n 0 B))
    (IteratedAsymptoticAlgebra.map n
      (NonUnitalCStarPullback.fstHom
        (ContinuousMap.IntervalGluing.evalAt B 1)
        (ContinuousMap.IntervalGluing.evalAt B 0)))
    (fstHom_comp_iteratedSplitPullbackEquiv n
      (ContinuousMap.IntervalGluing.evalAt B 1)
      (ContinuousMap.IntervalGluing.evalAt B 0)
      (ContinuousMap.IntervalGluing.constantHom B)
      (evalAt_zero_comp_constantHom B))

private theorem map_snd_comp_matchingEquiv_symm (n : ℕ)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (IteratedAsymptoticAlgebra.map n
      (NonUnitalCStarPullback.sndHom
        (ContinuousMap.IntervalGluing.evalAt B 1)
        (ContinuousMap.IntervalGluing.evalAt B 0))).comp
        (iteratedMatchingPathsEquiv n B).symm.toNonUnitalStarAlgHom =
      NonUnitalCStarPullback.sndHom
        (endpointHom n 1 B) (endpointHom n 0 B) := by
  exact comp_symm_eq_of_comp_eq
    (iteratedMatchingPathsEquiv n B)
    (NonUnitalCStarPullback.sndHom
      (endpointHom n 1 B) (endpointHom n 0 B))
    (IteratedAsymptoticAlgebra.map n
      (NonUnitalCStarPullback.sndHom
        (ContinuousMap.IntervalGluing.evalAt B 1)
        (ContinuousMap.IntervalGluing.evalAt B 0)))
    (sndHom_comp_iteratedSplitPullbackEquiv n
      (ContinuousMap.IntervalGluing.evalAt B 1)
      (ContinuousMap.IntervalGluing.evalAt B 0)
      (ContinuousMap.IntervalGluing.constantHom B)
      (evalAt_zero_comp_constantHom B))

/-- **Initial endpoint of finite-stage path gluing.**

For a nonunital complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient
C-star norm, and define α⁰X=X, αⁿ⁺¹X=α(αⁿX). For B a nonunital complex C-star algebra and n∈ℕ,
let P_B=C([0,1],B), e_s=αⁿ(ev_s):αⁿP_B→αⁿB, and M_n(B)={(x,y)∈αⁿP_B×αⁿP_B:e_1(x)=e_0(y)} with
its closed-subalgebra maximum norm. For G_n=glueHomN n B and projections pr_1,pr_2 from
M_n(B), e_0∘G_n=e_0∘pr_1.
-/
theorem endpointHom_zero_comp_glueHomN (n : ℕ)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (endpointHom n 0 B).comp (glueHomN n B) =
      (endpointHom n 0 B).comp
        (NonUnitalCStarPullback.fstHom
          (endpointHom n 1 B) (endpointHom n 0 B)) := by
  unfold endpointHom glueHomN
  rw [← NonUnitalStarAlgHom.comp_assoc,
    ← IteratedAsymptoticAlgebra.map_comp,
    evalAt_zero_comp_glueHom,
    IteratedAsymptoticAlgebra.map_comp,
    NonUnitalStarAlgHom.comp_assoc,
    map_fst_comp_matchingEquiv_symm]
  rfl

/-- **Terminal endpoint of finite-stage path gluing.**

For a nonunital complex C-star algebra X, put αX=C_b([1,∞),X)/C₀([1,∞),X) with its quotient
C-star norm, and define α⁰X=X, αⁿ⁺¹X=α(αⁿX). For B a nonunital complex C-star algebra and n∈ℕ,
let P_B=C([0,1],B), e_s=αⁿ(ev_s):αⁿP_B→αⁿB, and M_n(B)={(x,y)∈αⁿP_B×αⁿP_B:e_1(x)=e_0(y)} with
its closed-subalgebra maximum norm. For G_n=glueHomN n B and projections pr_1,pr_2 from
M_n(B), e_1∘G_n=e_1∘pr_2.
-/
theorem endpointHom_one_comp_glueHomN (n : ℕ)
    (B : Type uB) [NonUnitalCStarAlgebra B] :
    (endpointHom n 1 B).comp (glueHomN n B) =
      (endpointHom n 1 B).comp
        (NonUnitalCStarPullback.sndHom
          (endpointHom n 1 B) (endpointHom n 0 B)) := by
  unfold endpointHom glueHomN
  rw [← NonUnitalStarAlgHom.comp_assoc,
    ← IteratedAsymptoticAlgebra.map_comp,
    evalAt_one_comp_glueHom,
    IteratedAsymptoticAlgebra.map_comp,
    NonUnitalStarAlgHom.comp_assoc,
    map_snd_comp_matchingEquiv_symm]
  rfl


end AsymptoticAlgebra
