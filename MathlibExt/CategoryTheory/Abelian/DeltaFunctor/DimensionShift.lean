/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.Basic

/-!
# Dimension shifts for δ-functors

Exactness makes a connecting component monic or epic when the adjacent value
vanishes. In a balanced target category, vanishing of both neighboring values
at the middle object makes the connecting component an isomorphism.
Homological components lower degree and cohomological components raise it.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A]
variable {B : Type u₂} [Category.{v₂} B] [Preadditive B]

namespace HomologicalDeltaFunctor

variable (T : HomologicalDeltaFunctor A B)

/-- Vanishing of the higher middle-object value makes the lowering
connecting component monic. -/
lemma mono_connecting_of_isZero_middle_succ (n : ℕ)
    (S : ShortComplex.ShortExactSequences A)
    (h : IsZero ((T.T (n + 1)).obj S.obj.X₂)) :
    Mono ((T.connecting n).app S) := by
  obtain ⟨_, hS⟩ := T.exactRight n S
  exact hS.mono_g (h.eq_zero_of_src _)

/-- Vanishing of the lower middle-object value makes the lowering
connecting component epic. -/
lemma epi_connecting_of_isZero_middle (n : ℕ)
    (S : ShortComplex.ShortExactSequences A)
    (h : IsZero ((T.T n).obj S.obj.X₂)) :
    Epi ((T.connecting n).app S) := by
  obtain ⟨_, hS⟩ := T.exactLeft n S
  exact hS.epi_f (h.eq_zero_of_tgt _)

variable [Balanced B]

/-- The lowering boundary is a kernel of the following degree map
when the higher middle-object value vanishes. No chosen kernel is required. -/
noncomputable def connectingIsKernelOfIsZeroMiddleSucc (n : ℕ)
    (S : ShortComplex.ShortExactSequences A)
    (h : IsZero ((T.T (n + 1)).obj S.obj.X₂)) :
    IsLimit (KernelFork.ofι ((T.connecting n).app S)
      ((T.exactLeft n S).elim (fun w _ => w))) := by
  have hS : (ShortComplex.mk ((T.connecting n).app S) ((T.T n).map S.obj.f)
      ((T.exactLeft n S).elim (fun w _ => w))).Exact := by
    obtain ⟨_, hS⟩ := T.exactLeft n S
    exact hS
  have : Mono ((T.connecting n).app S) :=
    T.mono_connecting_of_isZero_middle_succ n S h
  exact hS.fIsKernel

/-- The lowering boundary is an isomorphism when the two adjacent
middle-object values vanish. -/
lemma isIso_connecting_of_isZero_middle (n : ℕ)
    (S : ShortComplex.ShortExactSequences A)
    (hn : IsZero ((T.T n).obj S.obj.X₂))
    (hs : IsZero ((T.T (n + 1)).obj S.obj.X₂)) :
    IsIso ((T.connecting n).app S) := by
  have : Mono ((T.connecting n).app S) :=
    T.mono_connecting_of_isZero_middle_succ n S hs
  have : Epi ((T.connecting n).app S) := T.epi_connecting_of_isZero_middle n S hn
  exact isIso_of_mono_of_epi _

/-- The dimension-shift isomorphism supplied by the lowering boundary. -/
noncomputable def connectingIsoOfIsZeroMiddle (n : ℕ)
    (S : ShortComplex.ShortExactSequences A)
    (hn : IsZero ((T.T n).obj S.obj.X₂))
    (hs : IsZero ((T.T (n + 1)).obj S.obj.X₂)) :
    (T.T (n + 1)).obj S.obj.X₃ ≅ (T.T n).obj S.obj.X₁ :=
  @asIso B _ _ _ ((T.connecting n).app S)
    (T.isIso_connecting_of_isZero_middle n S hn hs)

/-- The forward dimension-shift map is the given connecting component. -/
lemma connectingIsoOfIsZeroMiddle_hom (n : ℕ)
    (S : ShortComplex.ShortExactSequences A)
    (hn : IsZero ((T.T n).obj S.obj.X₂))
    (hs : IsZero ((T.T (n + 1)).obj S.obj.X₂)) :
    (T.connectingIsoOfIsZeroMiddle n S hn hs).hom = (T.connecting n).app S :=
  @asIso_hom B _ _ _ ((T.connecting n).app S)
    (T.isIso_connecting_of_isZero_middle n S hn hs)

end HomologicalDeltaFunctor

namespace CohomologicalDeltaFunctor

variable (T : CohomologicalDeltaFunctor A B)

/-- Vanishing of the lower middle-object value makes the raising
connecting component monic. -/
lemma mono_connecting_of_isZero_middle (n : ℕ)
    (S : ShortComplex.ShortExactSequences A)
    (h : IsZero ((T.T n).obj S.obj.X₂)) :
    Mono ((T.connecting n).app S) := by
  obtain ⟨_, hS⟩ := T.exactRight n S
  exact hS.mono_g (h.eq_zero_of_src _)

/-- Vanishing of the higher middle-object value makes the raising
connecting component epic. -/
lemma epi_connecting_of_isZero_middle_succ (n : ℕ)
    (S : ShortComplex.ShortExactSequences A)
    (h : IsZero ((T.T (n + 1)).obj S.obj.X₂)) :
    Epi ((T.connecting n).app S) := by
  obtain ⟨_, hS⟩ := T.exactLeft n S
  exact hS.epi_f (h.eq_zero_of_tgt _)

variable [Balanced B]

/-- The raising boundary is an isomorphism when the two adjacent
middle-object values vanish. -/
lemma isIso_connecting_of_isZero_middle (n : ℕ)
    (S : ShortComplex.ShortExactSequences A)
    (hn : IsZero ((T.T n).obj S.obj.X₂))
    (hs : IsZero ((T.T (n + 1)).obj S.obj.X₂)) :
    IsIso ((T.connecting n).app S) := by
  have : Mono ((T.connecting n).app S) := T.mono_connecting_of_isZero_middle n S hn
  have : Epi ((T.connecting n).app S) :=
    T.epi_connecting_of_isZero_middle_succ n S hs
  exact isIso_of_mono_of_epi _

/-- The dimension-shift isomorphism supplied by the raising boundary. -/
noncomputable def connectingIsoOfIsZeroMiddle (n : ℕ)
    (S : ShortComplex.ShortExactSequences A)
    (hn : IsZero ((T.T n).obj S.obj.X₂))
    (hs : IsZero ((T.T (n + 1)).obj S.obj.X₂)) :
    (T.T n).obj S.obj.X₃ ≅ (T.T (n + 1)).obj S.obj.X₁ :=
  @asIso B _ _ _ ((T.connecting n).app S)
    (T.isIso_connecting_of_isZero_middle n S hn hs)

/-- The forward dimension-shift map is the given connecting component. -/
lemma connectingIsoOfIsZeroMiddle_hom (n : ℕ)
    (S : ShortComplex.ShortExactSequences A)
    (hn : IsZero ((T.T n).obj S.obj.X₂))
    (hs : IsZero ((T.T (n + 1)).obj S.obj.X₂)) :
    (T.connectingIsoOfIsZeroMiddle n S hn hs).hom = (T.connecting n).app S :=
  @asIso_hom B _ _ _ ((T.connecting n).app S)
    (T.isIso_connecting_of_isZero_middle n S hn hs)

end CohomologicalDeltaFunctor

end CategoryTheory
