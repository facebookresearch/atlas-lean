/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusSectorContinuation
import Code.FrontierA.SurfaceKacWardTwist





namespace StatMech.FrontierA

open SimpleGraph StatMech.Onsager

private theorem triangularTorusDirectionStep_injective
    (L : Nat) [Fact (2 < L)] :
    Function.Injective (triangularTorusDirectionStep L) := by
  have h1 : (1 : ZMod L) ≠ 0 := by
    letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
    exact one_ne_zero
  have h2 : (2 : ZMod L) ≠ 0 := by
    rw [Ne, ← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have := (Fact.out : 2 < L)
    omega
  have hm1 : (-1 : ZMod L) ≠ 0 := neg_ne_zero.mpr h1
  have hpm : (1 : ZMod L) ≠ -1 := by
    intro h
    apply h2
    linear_combination h
  have h01 : (0 : ZMod L) ≠ 1 := Ne.symm h1
  have hmp : (-1 : ZMod L) ≠ 1 := Ne.symm hpm
  intro a b hab
  fin_cases a <;> fin_cases b <;>
    simp [triangularTorusDirectionStep, h1, hm1, hpm, h01, hmp] at hab ⊢

private theorem triangularTorusDart_adj
    (L : Nat) [Fact (2 < L)] (p : ZMod L × ZMod L) (a : Fin 6) :
    (triangularTorusGraph L).Adj p
      (p - triangularTorusDirectionStep L a) := by
  fin_cases a <;>
    simp [triangularTorusGraph, triangularTorusAdj, onsTorusAdj,
      triangularTorusDirectionStep] <;> ring



def triangularTorusDartToGraphDart
    (L : Nat) [Fact (2 < L)] :
    triangularTorusDart L → (triangularTorusGraph L).Dart :=
  fun d => ⟨(d.1, d.1 - triangularTorusDirectionStep L d.2),
    triangularTorusDart_adj L d.1 d.2⟩

private theorem triangularTorusDartToGraphDart_bijective
    (L : Nat) [Fact (2 < L)] :
    Function.Bijective (triangularTorusDartToGraphDart L) := by
  constructor
  · intro d e hde
    have hp : d.1 = e.1 := congrArg (fun z => z.fst) hde
    have hq : d.1 - triangularTorusDirectionStep L d.2 =
        e.1 - triangularTorusDirectionStep L e.2 :=
      congrArg (fun z => z.snd) hde
    apply Prod.ext hp
    apply triangularTorusDirectionStep_injective L
    rw [hp] at hq
    exact sub_right_injective hq
  · rintro ⟨⟨p, q⟩, hpq⟩
    change triangularTorusAdj L p q at hpq
    unfold triangularTorusAdj at hpq
    rcases hpq with hsquare | hdiag
    · rcases hsquare with ⟨h1, h2 | h2⟩ | ⟨h2, h1 | h1⟩
      · refine ⟨(p, (2 : Fin 6)), ?_⟩
        apply Dart.ext
        apply Prod.ext
        · rfl
        apply Prod.ext <;> simp [triangularTorusDartToGraphDart,
          triangularTorusDirectionStep] <;>
          first | linear_combination h1 | linear_combination h2
      · refine ⟨(p, (3 : Fin 6)), ?_⟩
        apply Dart.ext
        apply Prod.ext
        · rfl
        apply Prod.ext <;> simp [triangularTorusDartToGraphDart,
          triangularTorusDirectionStep] <;>
          first | linear_combination h1 | linear_combination h2
      · refine ⟨(p, (0 : Fin 6)), ?_⟩
        apply Dart.ext
        apply Prod.ext
        · rfl
        apply Prod.ext <;> simp [triangularTorusDartToGraphDart,
          triangularTorusDirectionStep] <;>
          first | linear_combination h1 | linear_combination h2
      · refine ⟨(p, (1 : Fin 6)), ?_⟩
        apply Dart.ext
        apply Prod.ext
        · rfl
        apply Prod.ext <;> simp [triangularTorusDartToGraphDart,
          triangularTorusDirectionStep] <;>
          first | linear_combination h1 | linear_combination h2
    · rcases hdiag with hdiag | hdiag
      · refine ⟨(p, (4 : Fin 6)), ?_⟩
        apply Dart.ext
        apply Prod.ext
        · rfl
        apply Prod.ext <;> simp [triangularTorusDartToGraphDart,
          triangularTorusDirectionStep] <;>
          first | linear_combination hdiag.1 | linear_combination hdiag.2
      · refine ⟨(p, (5 : Fin 6)), ?_⟩
        apply Dart.ext
        apply Prod.ext
        · rfl
        apply Prod.ext <;> simp [triangularTorusDartToGraphDart,
          triangularTorusDirectionStep] <;>
          first | linear_combination hdiag.1 | linear_combination hdiag.2



noncomputable def triangularTorusDartEquiv
    (L : Nat) [Fact (2 < L)] :
    triangularTorusDart L ≃ (triangularTorusGraph L).Dart :=
  Equiv.ofBijective (triangularTorusDartToGraphDart L)
    (triangularTorusDartToGraphDart_bijective L)

@[simp] theorem triangularTorusDartEquiv_apply
    (L : Nat) [Fact (2 < L)] (d : triangularTorusDart L) :
    triangularTorusDartEquiv L d = triangularTorusDartToGraphDart L d :=
  rfl

private theorem squareTorusHorizontalEdge_mk_iff
    (L : Nat) (p q : ZMod L × ZMod L) :
    squareTorusHorizontalEdge L s(p, q) ↔
      p.2 = q.2 ∧ (p.1 = q.1 + 1 ∨ p.1 = q.1 - 1) := by
  constructor
  · rintro ⟨r, hr⟩
    change s(p, q) = s(r, (r.1 + 1, r.2)) at hr
    rw [Sym2.eq_iff] at hr
    rcases hr with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨rfl, Or.inr (by ring)⟩
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨rfl, Or.inl rfl⟩
  · rintro ⟨h2, h1 | h1⟩
    · refine ⟨q, ?_⟩
      change s(p, q) = s(q, (q.1 + 1, q.2))
      rw [Sym2.eq_iff]
      exact Or.inr ⟨Prod.ext h1 h2, rfl⟩
    · refine ⟨p, ?_⟩
      change s(p, q) = s(p, (p.1 + 1, p.2))
      rw [Sym2.eq_iff]
      apply Or.inl
      refine ⟨rfl, Prod.ext ?_ h2.symm⟩
      simpa using (congrArg (fun z : ZMod L => z + 1) h1).symm

private theorem triangularTorusVerticalEdge_mk_iff
    (L : Nat) (p q : ZMod L × ZMod L) :
    triangularTorusVerticalEdge L s(p, q) ↔
      p.1 = q.1 ∧ (p.2 = q.2 + 1 ∨ p.2 = q.2 - 1) := by
  constructor
  · rintro ⟨r, hr⟩
    change s(p, q) = s(r, (r.1, r.2 + 1)) at hr
    rw [Sym2.eq_iff] at hr
    rcases hr with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨rfl, Or.inr (by ring)⟩
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨rfl, Or.inl rfl⟩
  · rintro ⟨h1, h2 | h2⟩
    · refine ⟨q, ?_⟩
      change s(p, q) = s(q, (q.1, q.2 + 1))
      rw [Sym2.eq_iff]
      exact Or.inr ⟨Prod.ext h1 h2, rfl⟩
    · refine ⟨p, ?_⟩
      change s(p, q) = s(p, (p.1, p.2 + 1))
      rw [Sym2.eq_iff]
      apply Or.inl
      refine ⟨rfl, Prod.ext h1.symm ?_⟩
      simpa using (congrArg (fun z : ZMod L => z + 1) h2).symm



theorem triangularTorusEdgeWeight_dart
    (L : Nat) [Fact (2 < L)] (t1 t2 t3 : Complex)
    (d : triangularTorusDart L) :
    triangularTorusEdgeWeight L t1 t2 t3
        (triangularTorusDartEquiv L d).edge =
      triangularTorusDirectionWeight t1 t2 t3 d.2 := by
  have h1 : (1 : ZMod L) ≠ 0 := by
    letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
    exact one_ne_zero
  have hshift (z : ZMod L) : z ≠ -1 + z := by
    intro h
    apply h1
    linear_combination h
  rcases d with ⟨p, a⟩
  fin_cases a
  all_goals simp [triangularTorusDartEquiv_apply,
      triangularTorusDartToGraphDart,
      SimpleGraph.Dart.edge, triangularTorusEdgeWeight,
      triangularTorusDirectionWeight, triangularTorusDirectionStep,
      squareTorusHorizontalEdge_mk_iff,
      triangularTorusVerticalEdge_mk_iff, h1] <;> try ring
  · intro hp
    exact (hshift p.2 hp).elim
  · rw [if_neg (hshift p.2), if_neg (hshift p.1)]


def triangularTorusDirectionReverse : Fin 6 → Fin 6 :=
  ![1, 0, 3, 2, 5, 4]

@[simp] theorem triangularTorusDirectionStep_reverse
    (L : Nat) (a : Fin 6) :
    triangularTorusDirectionStep L (triangularTorusDirectionReverse a) =
      -triangularTorusDirectionStep L a := by
  fin_cases a <;>
    simp [triangularTorusDirectionReverse, triangularTorusDirectionStep]


def triangularTorusDartReverse (L : Nat) :
    triangularTorusDart L → triangularTorusDart L :=
  fun d =>
    (d.1 - triangularTorusDirectionStep L d.2,
      triangularTorusDirectionReverse d.2)

@[simp] theorem triangularTorusDartEquiv_reverse
    (L : Nat) [Fact (2 < L)] (d : triangularTorusDart L) :
    triangularTorusDartEquiv L (triangularTorusDartReverse L d) =
      (triangularTorusDartEquiv L d).symm := by
  apply Dart.ext
  apply Prod.ext
  · rfl
  · simp [triangularTorusDartEquiv, triangularTorusDartReverse,
      triangularTorusDartToGraphDart]

@[simp] theorem triangularKacWardTurnMatrix_reverse_zero
    (rho : Complex) (a : Fin 6) :
    triangularKacWardTurnMatrix rho a
      (triangularTorusDirectionReverse a) = 0 := by
  fin_cases a <;>
    simp [triangularKacWardTurnMatrix, triangularTorusDirectionReverse]


noncomputable def triangularTorusGraphPhase
    (L : Nat) [Fact (2 < L)] (rho u v : Complex)
    (d e : (triangularTorusGraph L).Dart) : Complex :=
  let d' := (triangularTorusDartEquiv L).symm d
  let e' := (triangularTorusDartEquiv L).symm e
  triangularTorusDirectionPhase u v d'.2 *
    triangularKacWardTurnMatrix rho d'.2 e'.2


theorem kwGraphTransition_triangularTorusDartEquiv_apply
    (L : Nat) [Fact (2 < L)]
    (t1 t2 t3 rho u v : Complex) (d e : triangularTorusDart L) :
    kwGraphTransition (triangularTorusGraph L)
        (triangularTorusEdgeWeight L t1 t2 t3)
        (triangularTorusGraphPhase L rho u v)
        (triangularTorusDartEquiv L d) (triangularTorusDartEquiv L e) =
      if (triangularTorusDartEquiv L d).snd =
            (triangularTorusDartEquiv L e).fst ∧
          (triangularTorusDartEquiv L d).edge ≠
            (triangularTorusDartEquiv L e).edge then
        triangularTorusDirectionWeight t1 t2 t3 d.2 *
          (triangularTorusDirectionPhase u v d.2 *
            triangularKacWardTurnMatrix rho d.2 e.2)
      else 0 := by
  unfold kwGraphTransition
  split
  · rw [triangularTorusEdgeWeight_dart]
    unfold triangularTorusGraphPhase
    dsimp only
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  · rfl



theorem triangularTorusDartEquiv_consecutive_iff
    (L : Nat) [Fact (2 < L)] (d e : triangularTorusDart L) :
    (triangularTorusDartEquiv L d).snd =
        (triangularTorusDartEquiv L e).fst ↔
      (d.1.1 - e.1.1, d.1.2 - e.1.2) =
        triangularTorusDirectionStep L d.2 := by
  change d.1 - triangularTorusDirectionStep L d.2 = e.1 ↔
    d.1 - e.1 = triangularTorusDirectionStep L d.2
  constructor <;> intro h <;> rw [← h] <;> simp



theorem triangularTorusDartEquiv_edge_eq_iff_reverse
    (L : Nat) [Fact (2 < L)] (d e : triangularTorusDart L)
    (hc : (triangularTorusDartEquiv L d).snd =
      (triangularTorusDartEquiv L e).fst) :
    (triangularTorusDartEquiv L d).edge =
        (triangularTorusDartEquiv L e).edge ↔
      e = triangularTorusDartReverse L d := by
  constructor
  · intro hedge
    rcases (dart_edge_eq_iff
      (triangularTorusDartEquiv L d)
      (triangularTorusDartEquiv L e)).mp hedge with hsame | hsymm
    · exfalso
      apply (triangularTorusDartEquiv L d).fst_ne_snd
      calc
        (triangularTorusDartEquiv L d).fst =
            (triangularTorusDartEquiv L e).fst :=
          congrArg (fun z : (triangularTorusGraph L).Dart => z.fst) hsame
        _ = (triangularTorusDartEquiv L d).snd := hc.symm
    · apply (triangularTorusDartEquiv L).injective
      rw [triangularTorusDartEquiv_reverse]
      simpa using (congrArg Dart.symm hsymm).symm
  · rintro rfl
    rw [triangularTorusDartEquiv_reverse, Dart.edge_symm]



theorem triangularTorusKWMatrix_eq_reindex_graphTransition
    (L : Nat) [Fact (2 < L)]
    (t1 t2 t3 rho u v : Complex) :
    triangularTorusKWMatrix L t1 t2 t3 rho u v =
      (Matrix.reindex (triangularTorusDartEquiv L).symm
        (triangularTorusDartEquiv L).symm)
        (kwGraphTransition (triangularTorusGraph L)
          (triangularTorusEdgeWeight L t1 t2 t3)
          (triangularTorusGraphPhase L rho u v)) := by
  ext d e
  rw [Matrix.reindex_apply]
  change triangularTorusKWMatrix L t1 t2 t3 rho u v d e =
    kwGraphTransition (triangularTorusGraph L)
      (triangularTorusEdgeWeight L t1 t2 t3)
      (triangularTorusGraphPhase L rho u v)
      (triangularTorusDartEquiv L d) (triangularTorusDartEquiv L e)
  rw [kwGraphTransition_triangularTorusDartEquiv_apply]
  unfold triangularTorusKWMatrix ons_blockCirculant2D
    triangularTorusKWBlock
  by_cases hs : (d.1.1 - e.1.1, d.1.2 - e.1.2) =
      triangularTorusDirectionStep L d.2
  · rw [if_pos hs]
    have hc := (triangularTorusDartEquiv_consecutive_iff L d e).mpr hs
    by_cases he : e = triangularTorusDartReverse L d
    · subst e
      have hedge := (triangularTorusDartEquiv_edge_eq_iff_reverse
        L d (triangularTorusDartReverse L d) hc).mpr rfl
      rw [if_neg (fun h => h.2 hedge)]
      rw [show (triangularTorusDartReverse L d).2 =
        triangularTorusDirectionReverse d.2 from rfl,
        triangularKacWardTurnMatrix_reverse_zero]
      ring
    · have hedge : (triangularTorusDartEquiv L d).edge ≠
          (triangularTorusDartEquiv L e).edge := by
        intro h
        exact he ((triangularTorusDartEquiv_edge_eq_iff_reverse
          L d e hc).mp h)
      rw [if_pos ⟨hc, hedge⟩]
      ring
  · rw [if_neg hs]
    have hc : ¬(triangularTorusDartEquiv L d).snd =
        (triangularTorusDartEquiv L e).fst := fun h =>
      hs ((triangularTorusDartEquiv_consecutive_iff L d e).mp h)
    rw [if_neg (fun h => hc h.1)]




theorem det_one_sub_triangularTorusKWMatrix_eq_graphTransition
    (L : Nat) [Fact (2 < L)]
    (t1 t2 t3 rho u v : Complex) :
    (1 - triangularTorusKWMatrix L t1 t2 t3 rho u v).det =
      (1 - kwGraphTransition (triangularTorusGraph L)
        (triangularTorusEdgeWeight L t1 t2 t3)
        (triangularTorusGraphPhase L rho u v)).det := by
  rw [triangularTorusKWMatrix_eq_reindex_graphTransition]
  let e := (triangularTorusDartEquiv L).symm
  let M := kwGraphTransition (triangularTorusGraph L)
    (triangularTorusEdgeWeight L t1 t2 t3)
    (triangularTorusGraphPhase L rho u v)
  have hsub : 1 - Matrix.reindex e e M =
      Matrix.reindex e e (1 - M) := by
    ext d f
    simp [Matrix.reindex_apply, Matrix.one_apply]
  rw [hsub, Matrix.det_reindex_self]

end StatMech.FrontierA
