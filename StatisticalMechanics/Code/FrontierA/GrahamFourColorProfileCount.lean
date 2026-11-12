/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.GrahamLemmaOneFourColor
import Code.Sharpness.FluxEdgeCopyBridge

open Finset
open Classical

namespace StatMech.FrontierA

open StatMech.Sharpness.FluxEdgeCopy



theorem grahamFourColor_perFiber_count
    (alpha : Type*) [Fintype alpha] [DecidableEq alpha]
    (n k1 k2 k3 : Nat) (hn : Fintype.card alpha = n) :
    #((Finset.univ : Finset (GrahamFourColoring alpha)).filter (fun c =>
        c.IsPartition Finset.univ /\
          #c.color1 = k1 /\ #c.color2 = k2 /\ #c.color3 = k3)) =
      n.choose k1 * (n - k1).choose k2 *
        (n - k1 - k2).choose k3 := by
  let S := (Finset.univ : Finset (GrahamFourColoring alpha)).filter (fun c =>
    c.IsPartition Finset.univ /\
      #c.color1 = k1 /\ #c.color2 = k2 /\ #c.color3 = k3)
  let Aset := (Finset.univ : Finset alpha).powersetCard k1
  rw [show ((Finset.univ : Finset (GrahamFourColoring alpha)).filter (fun c =>
      c.IsPartition Finset.univ /\
        #c.color1 = k1 /\ #c.color2 = k2 /\ #c.color3 = k3)) = S by rfl]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun c : GrahamFourColoring alpha => c.color1) (t := Aset)
    (by
      intro c hc
      simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
        true_and] at hc
      simp only [Aset, Finset.mem_coe, Finset.mem_powersetCard]
      exact ⟨subset_univ _, hc.2.1⟩)]
  have hA : ∀ A, A ∈ Aset →
      #(S.filter (fun c => c.color1 = A)) =
        (n - k1).choose k2 * (n - k1 - k2).choose k3 := by
    intro A hAmem
    have hAdata : A ⊆ (Finset.univ : Finset alpha) /\ #A = k1 := by
      simpa [Aset] using hAmem
    let Bset := (Finset.univ \ A).powersetCard k2
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun c : GrahamFourColoring alpha => c.color2) (t := Bset)
      (by
        intro c hc
        simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
          true_and] at hc
        rcases hc with ⟨⟨hpart, _, hc2, _⟩, hcA⟩
        subst hcA
        simp only [Bset, Finset.mem_coe, Finset.mem_powersetCard]
        refine ⟨?_, hc2⟩
        intro x hx
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact fun hxA =>
          (Finset.disjoint_left.mp hpart.2.2.2.1) hxA hx)]
    have hB : ∀ B, B ∈ Bset →
        #((S.filter (fun c => c.color1 = A)).filter
            (fun c => c.color2 = B)) =
          (n - k1 - k2).choose k3 := by
      intro B hBmem
      have hBdata : B ⊆ Finset.univ \ A /\ #B = k2 := by
        simpa [Bset] using hBmem
      let Cset := (Finset.univ \ (A ∪ B)).powersetCard k3
      rw [show ((S.filter (fun c => c.color1 = A)).filter
            (fun c => c.color2 = B)) =
          Cset.image (fun C =>
            ({ color1 := A, color2 := B, color3 := C } :
              GrahamFourColoring alpha)) by
        ext c
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_image, Cset, Finset.mem_powersetCard]
        constructor
        · rintro ⟨⟨⟨hpart, hc1, hc2, hc3⟩, hca⟩, hcb⟩
          subst hca
          subst hcb
          refine ⟨c.color3, ⟨?_, hc3⟩, ?_⟩
          · intro x hx
            simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
              Finset.mem_union]
            exact fun hxAB => hxAB.elim
              (fun hxA =>
                (Finset.disjoint_left.mp hpart.2.2.2.2.1) hxA hx)
              (fun hxB =>
                (Finset.disjoint_left.mp hpart.2.2.2.2.2) hxB hx)
          · cases c
            rfl
        · rintro ⟨C, ⟨hCsub, hCcard⟩, rfl⟩
          have hAB : Disjoint A B := by
            rw [Finset.disjoint_left]
            intro x hxA hxB
            exact (Finset.mem_sdiff.mp (hBdata.1 hxB)).2 hxA
          have hAC : Disjoint A C := by
            rw [Finset.disjoint_left]
            intro x hxA hxC
            exact (Finset.mem_sdiff.mp (hCsub hxC)).2
              (Finset.mem_union_left B hxA)
          have hBC : Disjoint B C := by
            rw [Finset.disjoint_left]
            intro x hxB hxC
            exact (Finset.mem_sdiff.mp (hCsub hxC)).2
              (Finset.mem_union_right A hxB)
          exact ⟨⟨⟨⟨subset_univ _, subset_univ _, subset_univ _, hAB, hAC,
            hBC⟩, hAdata.2, hBdata.2, hCcard⟩, rfl⟩, rfl⟩]
      rw [Finset.card_image_of_injective]
      · rw [Finset.card_powersetCard]
        have hAB : Disjoint A B := by
          rw [Finset.disjoint_left]
          intro x hxA hxB
          exact (Finset.mem_sdiff.mp (hBdata.1 hxB)).2 hxA
        congr 1
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hn,
          Finset.card_union_of_disjoint hAB]
        omega
      · intro C D hCD
        exact congrArg GrahamFourColoring.color3 hCD
    rw [Finset.sum_congr rfl hB, Finset.sum_const, Finset.card_powersetCard]
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hn, hAdata.2]
    simp only [nsmul_eq_mul]
    simp
  rw [Finset.sum_congr rfl hA, Finset.sum_const, Finset.card_powersetCard]
  rw [Finset.card_univ, hn]
  simp only [nsmul_eq_mul, Nat.mul_assoc]
  simp

section SigmaPi

variable {E : Type*} [Fintype E] [DecidableEq E]
  {gamma : E -> Type*} [forall e, Fintype (gamma e)]
  [forall e, DecidableEq (gamma e)]

theorem graham_mem_sigmaFinsetEquivPi
    (S : Finset (Sigma fun e : E => gamma e)) (e : E) (x : gamma e) :
    x ∈ sigmaFinsetEquivPi S e <->
      (Sigma.mk e x : Sigma fun e : E => gamma e) ∈ S := by
  rw [show sigmaFinsetEquivPi S e =
      (Finset.univ : Finset (gamma e)).filter (fun x =>
        (Sigma.mk e x : Sigma fun e : E => gamma e) ∈ S) from rfl]
  simp



noncomputable def grahamFourColorSigmaEquivPi :
    GrahamFourColoring (Sigma fun e : E => gamma e) ≃
      (forall e : E, GrahamFourColoring (gamma e)) where
  toFun c := fun e =>
    { color1 := sigmaFinsetEquivPi c.color1 e
      color2 := sigmaFinsetEquivPi c.color2 e
      color3 := sigmaFinsetEquivPi c.color3 e }
  invFun c :=
    { color1 := sigmaFinsetEquivPi.symm (fun e => (c e).color1)
      color2 := sigmaFinsetEquivPi.symm (fun e => (c e).color2)
      color3 := sigmaFinsetEquivPi.symm (fun e => (c e).color3) }
  left_inv c := by
    cases c
    simp only [GrahamFourColoring.mk.injEq]
    constructor
    · rw [← Equiv.eq_symm_apply]
      rfl
    constructor <;> · rw [← Equiv.eq_symm_apply]; rfl
  right_inv c := by
    funext e
    cases h : c e
    simp only [Equiv.apply_symm_apply]
    rw [h]

theorem graham_disjoint_fiberwise
    (S T : Finset (Sigma fun e : E => gamma e)) :
    Disjoint S T <->
      forall e, Disjoint (sigmaFinsetEquivPi S e)
        (sigmaFinsetEquivPi T e) := by
  constructor
  · intro h e
    rw [Finset.disjoint_left]
    intro x hxS hxT
    rw [graham_mem_sigmaFinsetEquivPi] at hxS hxT
    exact (Finset.disjoint_left.mp h) hxS hxT
  · intro h
    rw [Finset.disjoint_left]
    rintro ⟨e, x⟩ hxS hxT
    have hxs : x ∈ sigmaFinsetEquivPi S e := by
      rw [graham_mem_sigmaFinsetEquivPi]
      exact hxS
    have hxt : x ∈ sigmaFinsetEquivPi T e := by
      rw [graham_mem_sigmaFinsetEquivPi]
      exact hxT
    exact (Finset.disjoint_left.mp (h e)) hxs hxt

theorem grahamFourColor_partition_fiberwise
    (c : GrahamFourColoring (Sigma fun e : E => gamma e)) :
    c.IsPartition Finset.univ <->
      forall e, (grahamFourColorSigmaEquivPi c e).IsPartition Finset.univ := by
  simp only [GrahamFourColoring.IsPartition, subset_univ, true_and]
  rw [graham_disjoint_fiberwise, graham_disjoint_fiberwise,
    graham_disjoint_fiberwise]
  constructor
  · rintro ⟨h12, h13, h23⟩ e
    exact ⟨h12 e, h13 e, h23 e⟩
  · intro h
    exact ⟨fun e => (h e).1, fun e => (h e).2.1,
      fun e => (h e).2.2⟩


noncomputable def grahamFourColorProfile
    (c : GrahamFourColoring (Sigma fun e : E => gamma e)) :
    (E -> Nat) × (E -> Nat) × (E -> Nat) :=
  (fun e => #(sigmaFinsetEquivPi c.color1 e),
    fun e => #(sigmaFinsetEquivPi c.color2 e),
    fun e => #(sigmaFinsetEquivPi c.color3 e))


theorem grahamFourColor_pi_profile_count (K1 K2 K3 : E -> Nat) :
    #((Finset.univ :
        Finset (GrahamFourColoring (Sigma fun e : E => gamma e))).filter
      (fun c => c.IsPartition Finset.univ /\
        grahamFourColorProfile c = (K1, K2, K3))) =
      ∏ e : E,
        (Fintype.card (gamma e)).choose (K1 e) *
          (Fintype.card (gamma e) - K1 e).choose (K2 e) *
          (Fintype.card (gamma e) - K1 e - K2 e).choose (K3 e) := by
  rw [show ((Finset.univ :
        Finset (GrahamFourColoring (Sigma fun e : E => gamma e))).filter
      (fun c => c.IsPartition Finset.univ /\
        grahamFourColorProfile c = (K1, K2, K3))) =
      (Fintype.piFinset (fun e =>
        (Finset.univ : Finset (GrahamFourColoring (gamma e))).filter
          (fun c => c.IsPartition Finset.univ /\
            #c.color1 = K1 e /\ #c.color2 = K2 e /\
              #c.color3 = K3 e))).image grahamFourColorSigmaEquivPi.symm by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hpart, hprof⟩
      refine ⟨grahamFourColorSigmaEquivPi c, ?_, ?_⟩
      · intro e
        have h1 := congrFun (congrArg Prod.fst hprof) e
        have h2 := congrFun (congrArg (fun p => p.2.1) hprof) e
        have h3 := congrFun (congrArg (fun p => p.2.2) hprof) e
        refine ⟨(grahamFourColor_partition_fiberwise c).mp hpart e,
          ?_, ?_, ?_⟩
        · change #(sigmaFinsetEquivPi c.color1 e) = K1 e
          simpa [grahamFourColorProfile] using h1
        · change #(sigmaFinsetEquivPi c.color2 e) = K2 e
          simpa [grahamFourColorProfile] using h2
        · change #(sigmaFinsetEquivPi c.color3 e) = K3 e
          simpa [grahamFourColorProfile] using h3
      · rw [Equiv.symm_apply_apply]
    · rintro ⟨f, hf, hfc⟩
      subst hfc
      have happ : grahamFourColorSigmaEquivPi
          (grahamFourColorSigmaEquivPi.symm f) = f :=
        Equiv.apply_symm_apply grahamFourColorSigmaEquivPi f
      have hpart : forall e,
          (grahamFourColorSigmaEquivPi
            (grahamFourColorSigmaEquivPi.symm f) e).IsPartition Finset.univ := by
        intro e
        rw [congrFun happ e]
        exact (hf e).1
      refine ⟨(grahamFourColor_partition_fiberwise _).mpr hpart, ?_⟩
      apply Prod.ext
      · funext e
        change #(grahamFourColorSigmaEquivPi
          (grahamFourColorSigmaEquivPi.symm f) e).color1 = K1 e
        rw [congrFun happ e]
        exact (hf e).2.1
      · apply Prod.ext
        · funext e
          change #(grahamFourColorSigmaEquivPi
            (grahamFourColorSigmaEquivPi.symm f) e).color2 = K2 e
          rw [congrFun happ e]
          exact (hf e).2.2.1
        · funext e
          change #(grahamFourColorSigmaEquivPi
            (grahamFourColorSigmaEquivPi.symm f) e).color3 = K3 e
          rw [congrFun happ e]
          exact (hf e).2.2.2]
  rw [Finset.card_image_of_injective _
    grahamFourColorSigmaEquivPi.symm.injective, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro e he
  exact grahamFourColor_perFiber_count (gamma e)
    (Fintype.card (gamma e)) (K1 e) (K2 e) (K3 e) rfl

end SigmaPi

section EdgeCopies

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]



theorem grahamFourColor_edgecopy_profile_count
    (total a b c : G.edgeFinset -> Nat) :
    #((grahamFourColorings
        (Finset.univ : Finset (Copy G total))).filter (fun q =>
      profileFlux G total q.color1 = a /\
        profileFlux G total q.color2 = b /\
        profileFlux G total q.color3 = c)) =
      ∏ e : G.edgeFinset,
        (total e).choose (a e) *
          (total e - a e).choose (b e) *
          (total e - a e - b e).choose (c e) := by
  simpa only [grahamFourColorings, Finset.filter_filter,
      grahamFourColorProfile, profileFlux,
      sigmaFinsetEquivPi_apply_card, Fintype.card_fin,
      and_assoc, Prod.mk.injEq] using
    (grahamFourColor_pi_profile_count
      (gamma := fun e : G.edgeFinset => Fin (total e)) a b c)



theorem grahamFourColor_profile_sum_le
    (total : G.edgeFinset -> Nat)
    (q : GrahamFourColoring (Copy G total))
    (hq : q.IsPartition Finset.univ) :
    forall e, profileFlux G total q.color1 e +
        profileFlux G total q.color2 e +
        profileFlux G total q.color3 e <= total e := by
  intro e
  let A := q.color1.filter (fun i : Copy G total => i.1 = e)
  let B := q.color2.filter (fun i : Copy G total => i.1 = e)
  let C := q.color3.filter (fun i : Copy G total => i.1 = e)
  have hAB : Disjoint A B := by
    exact Finset.disjoint_filter_filter hq.2.2.2.1
  have hAC : Disjoint A C := by
    exact Finset.disjoint_filter_filter hq.2.2.2.2.1
  have hBC : Disjoint B C := by
    exact Finset.disjoint_filter_filter hq.2.2.2.2.2
  have hABC : Disjoint (A ∪ B) C :=
    Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩
  have hsub : (A ∪ B) ∪ C ⊆
      (Finset.univ : Finset (Copy G total)).filter (fun i => i.1 = e) := by
    intro i hi
    simp only [Finset.mem_union] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hi with (hi | hi) | hi
    · exact (Finset.mem_filter.mp hi).2
    · exact (Finset.mem_filter.mp hi).2
    · exact (Finset.mem_filter.mp hi).2
  change #A + #B + #C <= total e
  rw [← Finset.card_union_of_disjoint hAB,
    ← Finset.card_union_of_disjoint hABC,
    ← fiber_card G total e]
  exact Finset.card_le_card hsub

theorem graham_profileFlux_union_disjoint
    (total : G.edgeFinset -> Nat) (S T : Finset (Copy G total))
    (hST : Disjoint S T) :
    profileFlux G total (S ∪ T) = fun e =>
      profileFlux G total S e + profileFlux G total T e := by
  funext e
  unfold profileFlux
  have hd : Disjoint
      (S.filter (fun i : Copy G total => i.1 = e))
      (T.filter (fun i : Copy G total => i.1 = e)) :=
    Finset.disjoint_filter_filter hST
  rw [← Finset.card_union_of_disjoint hd]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_union]
  tauto


theorem grahamFourColor_profile_color4
    (total : G.edgeFinset -> Nat)
    (q : GrahamFourColoring (Copy G total))
    (hq : q.IsPartition Finset.univ) :
    profileFlux G total (q.color4 Finset.univ) =
      fun e => total e - profileFlux G total q.color1 e -
        profileFlux G total q.color2 e -
        profileFlux G total q.color3 e := by
  unfold GrahamFourColoring.color4
  rw [profileFlux_compl]
  have h12 := graham_profileFlux_union_disjoint G total
    q.color1 q.color2 hq.2.2.2.1
  have h123 : Disjoint (q.color1 ∪ q.color2) q.color3 :=
    Finset.disjoint_union_left.mpr ⟨hq.2.2.2.2.1, hq.2.2.2.2.2⟩
  rw [graham_profileFlux_union_disjoint G total
    (q.color1 ∪ q.color2) q.color3 h123, h12]
  funext e
  have hle := grahamFourColor_profile_sum_le G total q hq e
  simp only
  omega

end EdgeCopies

end StatMech.FrontierA
