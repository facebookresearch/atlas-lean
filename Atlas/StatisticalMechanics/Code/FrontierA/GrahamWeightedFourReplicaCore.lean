/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Sharpness.MultiReplica

open Finset SimpleGraph
open scoped BigOperators
open Classical

set_option maxHeartbeats 8000000

namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]



def grahamQuadEquivSigma {E : Type*} :
    ((E -> Nat) × (E -> Nat) × (E -> Nat) × (E -> Nat)) ≃
      Sigma (fun total : E -> Nat =>
        {pqr : (E -> Nat) × (E -> Nat) × (E -> Nat) //
          ∀ e, pqr.1 e + pqr.2.1 e + pqr.2.2 e ≤ total e}) where
  toFun z :=
    ⟨fun e => z.1 e + z.2.1 e + z.2.2.1 e + z.2.2.2 e,
      ⟨(z.1, z.2.1, z.2.2.1), fun e => by simp only; omega⟩⟩
  invFun s :=
    (s.2.1.1, s.2.1.2.1, s.2.1.2.2,
      fun e => s.1 e - s.2.1.1 e - s.2.1.2.1 e - s.2.1.2.2 e)
  left_inv := by
    rintro ⟨a, b, c, d⟩
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
    funext e
    simp only
    omega
  right_inv := by
    rintro ⟨total, ⟨⟨a, b, c⟩, habc⟩⟩
    have htotal :
        (fun e => a e + b e + c e +
          (total e - a e - b e - c e)) = total := by
      funext e
      have h := habc e
      dsimp at h ⊢
      omega
    exact Sigma.subtype_ext htotal (by simp only)



def grahamPairPairEquivSigma {E : Type*} :
    (((E -> Nat) × (E -> Nat)) × ((E -> Nat) × (E -> Nat))) ≃
      Sigma (fun total : E -> Nat =>
        {pqr : (E -> Nat) × (E -> Nat) × (E -> Nat) //
          ∀ e, pqr.1 e + pqr.2.1 e + pqr.2.2 e ≤ total e}) :=
  ({ toFun := fun z => (z.1.1, z.1.2, z.2.1, z.2.2)
     invFun := fun z => ((z.1, z.2.1), (z.2.2.1, z.2.2.2))
     left_inv := by rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl
     right_inv := by rintro ⟨a, b, c, d⟩; rfl } :
    (((E -> Nat) × (E -> Nat)) × ((E -> Nat) × (E -> Nat))) ≃
      ((E -> Nat) × (E -> Nat) × (E -> Nat) × (E -> Nat))).trans
    grahamQuadEquivSigma


noncomputable instance grahamFintypeQuadLe
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (total : G.edgeFinset -> Nat) :
    Fintype {pqr : (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat) ×
        (G.edgeFinset -> Nat) //
      ∀ e, pqr.1 e + pqr.2.1 e + pqr.2.2 e ≤ total e} := by
  let embed := fun s : {pqr : (G.edgeFinset -> Nat) ×
      (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat) //
      ∀ e, pqr.1 e + pqr.2.1 e + pqr.2.2 e ≤ total e} =>
    (fun e => (⟨s.1.1 e, by have := s.2 e; omega⟩ : Fin (total e + 1)),
      fun e => (⟨s.1.2.1 e, by have := s.2 e; omega⟩ : Fin (total e + 1)),
      fun e => (⟨s.1.2.2 e, by have := s.2 e; omega⟩ : Fin (total e + 1)))
  letI : Finite {pqr : (G.edgeFinset -> Nat) ×
      (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat) //
      ∀ e, pqr.1 e + pqr.2.1 e + pqr.2.2 e ≤ total e} :=
    Finite.of_injective embed (by
      intro a b h
      apply Subtype.ext
      apply Prod.ext
      · funext e
        have he := congrFun (congrArg Prod.fst h) e
        simpa [embed] using he
      · apply Prod.ext
        · funext e
          have he := congrFun (congrArg (fun z => z.2.1) h) e
          simpa [embed] using he
        · funext e
          have he := congrFun (congrArg (fun z => z.2.2) h) e
          simpa [embed] using he)
  exact Fintype.ofFinite _


theorem grahamOfEdgeFun_add4
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b c d : G.edgeFinset -> Nat) :
    (fun e => ofEdgeFun G a e + ofEdgeFun G b e +
      ofEdgeFun G c e + ofEdgeFun G d e) =
      ofEdgeFun G (fun e => a e + b e + c e + d e) := by
  ext e
  unfold ofEdgeFun
  by_cases he : e ∈ G.edgeFinset <;> simp [he]



theorem grahamWeight_mul4_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (a b c d : Current V) :
    weight G beta J a * weight G beta J b *
        weight G beta J c * weight G beta J d =
      (∏ e ∈ G.edgeFinset,
        (Nat.choose (a e + b e + c e + d e) (a e) : Real) *
          (Nat.choose (b e + c e + d e) (b e) : Real) *
          (Nat.choose (c e + d e) (c e) : Real)) *
        weight G beta J (fun e => a e + b e + c e + d e) := by
  have hcd := weight_mul_eq G beta J c d
  have hbcd := weight_mul_eq G beta J b (fun e => c e + d e)
  have habcd := weight_mul_eq G beta J a
    (fun e => b e + c e + d e)
  calc
    weight G beta J a * weight G beta J b *
        weight G beta J c * weight G beta J d =
      weight G beta J a *
        (weight G beta J b * (weight G beta J c * weight G beta J d)) := by
          ring
    _ = weight G beta J a * (weight G beta J b *
        ((∏ e ∈ G.edgeFinset,
          (Nat.choose (c e + d e) (c e) : Real)) *
            weight G beta J (fun e => c e + d e))) := by rw [hcd]
    _ = (∏ e ∈ G.edgeFinset,
          (Nat.choose (c e + d e) (c e) : Real)) *
        (weight G beta J a *
          (weight G beta J b * weight G beta J (fun e => c e + d e))) := by
            ring
    _ = (∏ e ∈ G.edgeFinset,
          (Nat.choose (c e + d e) (c e) : Real)) *
        (weight G beta J a *
          ((∏ e ∈ G.edgeFinset,
            (Nat.choose (b e + (c e + d e)) (b e) : Real)) *
              weight G beta J (fun e => b e + (c e + d e)))) := by
                rw [hbcd]
    _ = (∏ e ∈ G.edgeFinset,
          (Nat.choose (c e + d e) (c e) : Real)) *
        (∏ e ∈ G.edgeFinset,
          (Nat.choose (b e + c e + d e) (b e) : Real)) *
        (weight G beta J a *
          weight G beta J (fun e => b e + c e + d e)) := by ring
    _ = (∏ e ∈ G.edgeFinset,
          (Nat.choose (c e + d e) (c e) : Real)) *
        (∏ e ∈ G.edgeFinset,
          (Nat.choose (b e + c e + d e) (b e) : Real)) *
        ((∏ e ∈ G.edgeFinset,
          (Nat.choose (a e + (b e + c e + d e)) (a e) : Real)) *
            weight G beta J (fun e => a e + (b e + c e + d e))) := by
              rw [habcd]
    _ = _ := by
      have hprod :
          (∏ e ∈ G.edgeFinset,
              (Nat.choose (c e + d e) (c e) : Real)) *
            (∏ e ∈ G.edgeFinset,
              (Nat.choose (b e + c e + d e) (b e) : Real)) *
            (∏ e ∈ G.edgeFinset,
              (Nat.choose (a e + (b e + c e + d e)) (a e) : Real)) =
          ∏ e ∈ G.edgeFinset,
            (Nat.choose (a e + b e + c e + d e) (a e) : Real) *
              (Nat.choose (b e + c e + d e) (b e) : Real) *
              (Nat.choose (c e + d e) (c e) : Real) := by
        rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro e he
        ring
      rw [show (fun e => a e + (b e + c e + d e)) =
          (fun e => a e + b e + c e + d e) by
        funext e; omega]
      calc
        ((∏ e ∈ G.edgeFinset,
              (Nat.choose (c e + d e) (c e) : Real)) *
            (∏ e ∈ G.edgeFinset,
              (Nat.choose (b e + c e + d e) (b e) : Real))) *
            ((∏ e ∈ G.edgeFinset,
              (Nat.choose (a e + (b e + c e + d e)) (a e) : Real)) *
              weight G beta J (fun e => a e + b e + c e + d e)) =
          ((∏ e ∈ G.edgeFinset,
              (Nat.choose (c e + d e) (c e) : Real)) *
            (∏ e ∈ G.edgeFinset,
              (Nat.choose (b e + c e + d e) (b e) : Real)) *
            (∏ e ∈ G.edgeFinset,
              (Nat.choose (a e + (b e + c e + d e)) (a e) : Real))) *
              weight G beta J (fun e => a e + b e + c e + d e) := by ring
        _ = _ := by rw [hprod]



theorem grahamWeight_split4_eq_binom
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (total a b c : G.edgeFinset -> Nat)
    (habc : ∀ e, a e + b e + c e ≤ total e) :
    weight G beta J (ofEdgeFun G a) *
        weight G beta J (ofEdgeFun G b) *
        weight G beta J (ofEdgeFun G c) *
        weight G beta J
          (ofEdgeFun G (fun e => total e - a e - b e - c e)) =
      (∏ e : G.edgeFinset,
        (Nat.choose (total e) (a e) : Real) *
          (Nat.choose (total e - a e) (b e) : Real) *
          (Nat.choose (total e - a e - b e) (c e) : Real)) *
        weight G beta J (ofEdgeFun G total) := by
  let d : G.edgeFinset -> Nat :=
    fun e => total e - a e - b e - c e
  have hsplit : ofEdgeFun G total =
      fun e => ofEdgeFun G a e + ofEdgeFun G b e +
        ofEdgeFun G c e + ofEdgeFun G d e := by
    rw [grahamOfEdgeFun_add4]
    congr 1
    funext e
    dsimp [d]
    have h := habc e
    omega
  rw [grahamWeight_mul4_eq G beta J]
  apply congrArg₂ (· * ·)
  · rw [← Finset.prod_attach G.edgeFinset]
    apply Finset.prod_congr rfl
    intro e he
    have h := habc e
    simp only [ofEdgeFun, dif_pos e.2]
    dsimp [d]
    have h0 : a e + b e + c e +
        (total e - a e - b e - c e) = total e := by omega
    have h1 : b e + c e + (total e - a e - b e - c e) =
        total e - a e := by omega
    have h2 : c e + (total e - a e - b e - c e) =
        total e - a e - b e := by omega
    rw [h0, h1, h2]
  · dsimp [d] at hsplit
    exact congrArg (weight G beta J) hsplit.symm

end StatMech.FrontierA
