/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectBoundaryToggleWinding
import Code.FrontierD.FKRectConnectedInsertionSurfaceAssembly
import Code.FrontierD.FKRectMedialLoopTurnGeometry
import Code.FrontierD.FKRectRefinedConnectedInsertionCarrier



open Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section

private theorem cyclicPred_injective {N : Nat} (hN : 0 < N) :
    Function.Injective (SixVertexArrows.cyclicPred hN) := by
  intro x y h
  rw [← finitePeriodicSucc_cyclicPred hN x,
    ← finitePeriodicSucc_cyclicPred hN y, h]

private theorem even_cyclicPred_iff_not {N : Nat} (hN : 0 < N)
    (hEven : Even N) (i : Fin N) :
    Even (SixVertexArrows.cyclicPred hN i).val ↔ ¬ Even i.val := by
  let z := SixVertexArrows.cyclicPred hN i
  have hsucc : Even (finitePeriodicSucc hN z).val ↔ ¬ Even z.val := by
    change Even ((z.val + 1) % N) ↔ ¬ Even z.val
    rw [Even.mod_even_iff hEven, Nat.even_add_one]
  rw [finitePeriodicSucc_cyclicPred] at hsucc
  tauto

private theorem cyclicPred_val {N : Nat} (hN : 0 < N) (i : Fin N) :
    (SixVertexArrows.cyclicPred hN i).val =
      if i.val = 0 then N - 1 else i.val - 1 := by
  unfold SixVertexArrows.cyclicPred
  simp only [Fin.val_mk]
  by_cases hi : i.val = 0
  · rw [if_pos hi, hi, zero_add,
      Nat.mod_eq_of_lt (Nat.sub_lt hN Nat.zero_lt_one)]
  · rw [if_neg hi]
    have hiPos : 0 < i.val := Nat.pos_of_ne_zero hi
    have heq : i.val + N - 1 = (i.val - 1) + N := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt]
    omega

private theorem cyclicPred_cyclicPred_ne_self {N : Nat}
    (hN : 2 < N) (i : Fin N) :
    SixVertexArrows.cyclicPred (by omega)
        (SixVertexArrows.cyclicPred (by omega) i) ≠ i := by
  intro h
  have hval := congrArg Fin.val h
  let p := SixVertexArrows.cyclicPred (by omega : 0 < N) i
  have hp := cyclicPred_val (N := N) (by omega) i
  have hpp := cyclicPred_val (N := N) (by omega) p
  by_cases hi0 : i.val = 0
  · rw [if_pos hi0] at hp
    have hp0 : p.val ≠ 0 := by dsimp [p] at hp ⊢; omega
    rw [if_neg hp0] at hpp
    dsimp [p] at hpp hval
    omega
  · rw [if_neg hi0] at hp
    by_cases hi1 : i.val = 1
    · have hp0 : p.val = 0 := by dsimp [p] at hp ⊢; omega
      rw [if_pos hp0] at hpp
      dsimp [p] at hpp hval
      omega
    · have hp0 : p.val ≠ 0 := by dsimp [p] at hp ⊢; omega
      rw [if_neg hp0] at hpp
      dsimp [p] at hpp hval
      omega

set_option maxHeartbeats 1000000 in
theorem fkRectTorusIndexedEdge_injective (R : FKRectTorus) :
    Function.Injective (fkRectTorusIndexedEdge R) := by
  rintro ⟨b, x, y⟩ ⟨c, u, v⟩ h
  cases b <;> cases c <;>
    by_cases hy : Even y.val <;> by_cases hv : Even v.val <;>
    simp [fkRectTorusIndexedEdge, hy, hv, Sym2.eq_iff] at h ⊢
  all_goals
    have hxne := cyclicPred_ne_self
      (lt_trans Nat.one_lt_two R.width_gt_two)
    have hyne := cyclicPred_ne_self
      (lt_trans Nat.one_lt_two R.height_gt_two)
    have hypred := even_cyclicPred_iff_not R.height_pos R.height_even
    have hxinj := cyclicPred_injective R.width_pos
    have hyinj := cyclicPred_injective R.height_pos
    have hxtwo := cyclicPred_cyclicPred_ne_self R.width_gt_two
    have hytwo := cyclicPred_cyclicPred_ne_self R.height_gt_two
    rcases h with ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ | ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    all_goals aesop (config := { maxRuleApplications := 50 })
    all_goals exact hxne _ h3.symm


def fkRectInsertedEdgeStepCharge (R : FKRectTorus) (e : R.EdgeIndex)
    (x y : R.Vertex) : Int :=
  if x = fkRectMedialWestPrimal R e ∧
      y = fkRectMedialEastPrimal R e then -1
  else if x = fkRectMedialEastPrimal R e ∧
      y = fkRectMedialWestPrimal R e then 1
  else 0


def fkRectInsertedEdgeCharge (R : FKRectTorus) (e : R.EdgeIndex)
    {G : SimpleGraph R.Vertex} {x y : R.Vertex} : G.Walk x y → Int
  | .nil' _ => 0
  | .cons' x z _ _ p =>
      fkRectInsertedEdgeStepCharge R e x z +
        fkRectInsertedEdgeCharge R e p

private theorem fkRectInsertedEdgeStepCharge_eq_zero_of_old_adj
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F) {x y : R.Vertex}
    (hxy : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Adj x y) :
    fkRectInsertedEdgeStepCharge R e x y = 0 := by
  obtain ⟨f, hf, hedge⟩ := hxy
  unfold fkRectInsertedEdgeStepCharge
  by_cases hforward : x = fkRectMedialWestPrimal R e ∧
      y = fkRectMedialEastPrimal R e
  · exfalso
    apply heF
    have hfe : f = e := fkRectTorusIndexedEdge_injective R <| by
      rw [hedge, fkRectTorusIndexedEdge_eq_medialPrimals]
      rcases hforward with ⟨rfl, rfl⟩
      rfl
    simpa [fkRectConfigurationOfEdges, hfe] using hf
  · rw [if_neg hforward]
    by_cases hreverse : x = fkRectMedialEastPrimal R e ∧
        y = fkRectMedialWestPrimal R e
    · exfalso
      apply heF
      have hfe : f = e := fkRectTorusIndexedEdge_injective R <| by
        rw [hedge, fkRectTorusIndexedEdge_eq_medialPrimals]
        rcases hreverse with ⟨rfl, rfl⟩
        exact Sym2.eq_swap
      simpa [fkRectConfigurationOfEdges, hfe] using hf
    · rw [if_neg hreverse]

theorem fkRectInsertedEdgeCharge_eq_zero_of_oldWalk
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F) {x y : R.Vertex}
    (p : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk x y) :
    fkRectInsertedEdgeCharge R e p = 0 := by
  induction p with
  | nil => rfl
  | @cons x y z hxy p ih =>
      simp only [fkRectInsertedEdgeCharge]
      rw [fkRectInsertedEdgeStepCharge_eq_zero_of_old_adj R F e heF hxy,
        zero_add, ih]



theorem fkRectWalkWinding_insert_eq_old_add_charge
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (heF : e ∉ F) {u v : R.Vertex}
    (p : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R (insert e F))).Walk u v) :
    ∃ q : (fkRectOpenGraph R
        (fkRectConfigurationOfEdges R F)).Walk u v,
      fkRectWalkWinding R p =
        fkRectWalkWinding R q +
          fkRectInsertedEdgeCharge R e p •
            fkRectWalkWinding R
              (fkRectInsertedFundamentalWalk R F e r) := by
  let G := fkRectOpenGraph R (fkRectConfigurationOfEdges R F)
  let H := fkRectOpenGraph R
    (fkRectConfigurationOfEdges R (insert e F))
  let a := fkRectMedialWestPrimal R e
  let b := fkRectMedialEastPrimal R e
  have hab : fkRectTorusIndexedEdge R e = s(a, b) :=
    fkRectTorusIndexedEdge_eq_medialPrimals R e
  have hgraph : H = G ⊔ SimpleGraph.edge a b :=
    fkRectOpenGraph_configurationOfEdges_insert R F e hab
  have hfund : fkRectWalkWinding R
      (fkRectInsertedFundamentalWalk R F e r) =
        fkRectWalkWinding R r + fkRectStepWinding R b a := by
    rw [fkRectInsertedFundamentalWalk_winding]
    rfl
  induction p with
  | nil =>
      refine ⟨.nil, ?_⟩
      simp [fkRectWalkWinding, fkRectInsertedEdgeCharge]
  | @cons x y z hxy p ih =>
      obtain ⟨q, hq⟩ := ih
      have hxy' : (G ⊔ SimpleGraph.edge a b).Adj x y := by
        rw [← hgraph]
        exact hxy
      rw [SimpleGraph.sup_adj] at hxy'
      rcases hxy' with hold | hnew
      · refine ⟨.cons hold q, ?_⟩
        simp only [fkRectWalkWinding, fkRectInsertedEdgeCharge]
        rw [fkRectInsertedEdgeStepCharge_eq_zero_of_old_adj
          R F e heF hold, zero_add, hq]
        apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, zsmul_eq_mul] <;> ring
      · rw [SimpleGraph.edge_adj] at hnew
        rcases hnew.1 with hforward | hreverse
        · rcases hforward with ⟨rfl, rfl⟩
          refine ⟨r.append q, ?_⟩
          simp only [fkRectWalkWinding, fkRectWalkWinding_append,
            fkRectInsertedEdgeCharge]
          rw [show fkRectInsertedEdgeStepCharge R e a b = -1 by
            simp [fkRectInsertedEdgeStepCharge, a, b], hq, hfund]
          have hswap := fkRectStepWinding_swap R a b
          apply Prod.ext
          · have hx := congrArg Prod.fst hswap
            simp only [Prod.fst_neg] at hx
            simp only [Prod.fst_add, Prod.smul_fst, zsmul_eq_mul]
            dsimp [fkRectStepWinding] at hx ⊢
            ring_nf at hx ⊢
            linear_combination hx
          · have hy := congrArg Prod.snd hswap
            simp only [Prod.snd_neg] at hy
            simp only [Prod.snd_add, Prod.smul_snd, zsmul_eq_mul]
            dsimp [fkRectStepWinding] at hy ⊢
            ring_nf at hy ⊢
            linear_combination hy
        · rcases hreverse with ⟨rfl, rfl⟩
          refine ⟨r.reverse.append q, ?_⟩
          have habne : a ≠ b := by
            intro heq
            apply fkRectTorusIndexedEdge_ne_diag R e a
            simpa [heq] using hab
          simp only [fkRectWalkWinding, fkRectWalkWinding_append,
            fkRectWalkWinding_reverse, fkRectInsertedEdgeCharge]
          rw [show fkRectInsertedEdgeStepCharge R e b a = 1 by
            simp [fkRectInsertedEdgeStepCharge, a, b, habne], hq, hfund]
          apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add,
            Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd,
            zsmul_eq_mul, Prod.fst_mul, Prod.snd_mul,
            Prod.fst_intCast, Prod.snd_intCast, Int.cast_id,
            fkRectStepWinding] <;> ring

theorem fkRectMedialBoundaryStep_label_eq_or_indexedEdge
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    fkRectMedialDartPrimalLabel R d =
        fkRectMedialDartPrimalLabel R
          (fkMedialBoundaryStep
            (fkRectConfigurationToMedialPairing R omega) d) ∨
      fkRectTorusIndexedEdge R
          (fkRectTorusMedialEdgeEquiv R d.1) =
        s(fkRectMedialDartPrimalLabel R d,
          fkRectMedialDartPrimalLabel R
            (fkMedialBoundaryStep
              (fkRectConfigurationToMedialPairing R omega) d)) := by
  rw [fkMedialBoundaryStep_apply,
    fkRectMedialDartPrimalLabel_bondMate]
  rcases d with ⟨v, side⟩
  let f := fkRectTorusMedialEdgeEquiv R v
  have hedge : fkRectTorusIndexedEdge R f =
      s(fkRectMedialWestPrimal R f, fkRectMedialEastPrimal R f) :=
    fkRectTorusIndexedEdge_eq_medialPrimals R f
  cases hopen : omega f <;>
    cases hp : fkRectClosedPairingAtEdge f <;> cases side
  all_goals
    simp only [fkRectConfigurationToMedialPairing_apply, f] at *
  all_goals
    simp [fkRectMedialDartPrimalLabel, fkMedialLocalMate, hopen, hp]
  all_goals
    first
    | exact Or.inl rfl
    | exact Or.inr hedge
    | exact Or.inr (hedge.trans Sym2.eq_swap)

theorem fkRectInsertedEdgeCharge_append
    (R : FKRectTorus) (e : R.EdgeIndex)
    {G : SimpleGraph R.Vertex} {x y z : R.Vertex}
    (p : G.Walk x y) (q : G.Walk y z) :
    fkRectInsertedEdgeCharge R e (p.append q) =
      fkRectInsertedEdgeCharge R e p +
        fkRectInsertedEdgeCharge R e q := by
  induction p with
  | nil => simp [fkRectInsertedEdgeCharge]
  | @cons a b c hab p ih =>
      simp only [Walk.cons_append, fkRectInsertedEdgeCharge]
      rw [ih]
      ring

theorem fkRectInsertedEdgeCharge_copy
    (R : FKRectTorus) (e : R.EdgeIndex)
    {G : SimpleGraph R.Vertex} {x y x' y' : R.Vertex}
    (p : G.Walk x y) (hx : x = x') (hy : y = y') :
    fkRectInsertedEdgeCharge R e (p.copy hx hy) =
      fkRectInsertedEdgeCharge R e p := by
  subst x'
  subst y'
  rfl

theorem fkRectInsertedEdgeCharge_boundaryStepWalk
    (R : FKRectTorus) (omega : R.Configuration) (e : R.EdgeIndex)
    (d : FKMedialDart R.medialTorus) :
    fkRectInsertedEdgeCharge R e
        (fkRectMedialBoundaryPrimalStepWalk R omega d) =
      fkRectInsertedEdgeStepCharge R e
        (fkRectMedialDartPrimalLabel R d)
        (fkRectMedialDartPrimalLabel R
          (fkMedialBoundaryStep
            (fkRectConfigurationToMedialPairing R omega) d)) := by
  unfold fkRectMedialBoundaryPrimalStepWalk
  split
  next heq =>
    rw [fkRectInsertedEdgeCharge_copy]
    simp only [fkRectInsertedEdgeCharge]
    unfold fkRectInsertedEdgeStepCharge
    rw [← heq]
    have hne : fkRectMedialWestPrimal R e ≠
        fkRectMedialEastPrimal R e := by
      intro h
      apply fkRectTorusIndexedEdge_ne_diag R e
        (fkRectMedialWestPrimal R e)
      simpa [h] using fkRectTorusIndexedEdge_eq_medialPrimals R e
    split_ifs with hforward hreverse
    · exfalso
      exact hne (hforward.1.symm.trans hforward.2)
    · exfalso
      exact hne (hreverse.2.symm.trans hreverse.1)
    · rfl
  next hne =>
    simp [fkRectInsertedEdgeCharge]

theorem fkRectInsertedEdgeCharge_boundaryTrace
    (R : FKRectTorus) (omega : R.Configuration) (e : R.EdgeIndex)
    (d : FKMedialDart R.medialTorus) (n : Nat) :
    fkRectInsertedEdgeCharge R e
        (fkRectMedialBoundaryPrimalTrace R omega d n) =
      ∑ i ∈ Finset.range n,
        fkRectInsertedEdgeStepCharge R e
          (fkRectMedialDartPrimalLabel R
            ((fkMedialBoundaryStep
              (fkRectConfigurationToMedialPairing R omega))^[i] d))
          (fkRectMedialDartPrimalLabel R
            ((fkMedialBoundaryStep
              (fkRectConfigurationToMedialPairing R omega))^[i + 1] d)) := by
  induction n generalizing d with
  | zero => simp [fkRectMedialBoundaryPrimalTrace,
      fkRectInsertedEdgeCharge]
  | succ n ih =>
      rw [fkRectMedialBoundaryPrimalTrace]
      simp only [id_eq]
      have happ := fkRectInsertedEdgeCharge_append R e
        (fkRectMedialBoundaryPrimalStepWalk R omega d)
        (fkRectMedialBoundaryPrimalTrace R omega
          (fkMedialBoundaryStep
            (fkRectConfigurationToMedialPairing R omega) d) n)
      calc
        _ = fkRectInsertedEdgeCharge R e
              (fkRectMedialBoundaryPrimalStepWalk R omega d) +
            fkRectInsertedEdgeCharge R e
              (fkRectMedialBoundaryPrimalTrace R omega
                (fkMedialBoundaryStep
                  (fkRectConfigurationToMedialPairing R omega) d) n) := happ
        _ = _ := by
          rw [fkRectInsertedEdgeCharge_boundaryStepWalk, ih]
          rw [Finset.sum_range_succ']
          simp only [Function.iterate_zero_apply]
          have hshift :
              (∑ i ∈ Finset.range n,
                fkRectInsertedEdgeStepCharge R e
                  (fkRectMedialDartPrimalLabel R
                    ((fkMedialBoundaryStep
                      (fkRectConfigurationToMedialPairing R omega))^[i]
                        (fkMedialBoundaryStep
                          (fkRectConfigurationToMedialPairing R omega) d)))
                  (fkRectMedialDartPrimalLabel R
                    ((fkMedialBoundaryStep
                      (fkRectConfigurationToMedialPairing R omega))^[i + 1]
                        (fkMedialBoundaryStep
                          (fkRectConfigurationToMedialPairing R omega) d)))) =
            ∑ i ∈ Finset.range n,
                fkRectInsertedEdgeStepCharge R e
                  (fkRectMedialDartPrimalLabel R
                    ((fkMedialBoundaryStep
                      (fkRectConfigurationToMedialPairing R omega))^[i + 1] d))
                  (fkRectMedialDartPrimalLabel R
                    ((fkMedialBoundaryStep
                      (fkRectConfigurationToMedialPairing R omega))^[i + 2] d)) := by
            apply Finset.sum_congr rfl
            intro i hi
            let f := fkMedialBoundaryStep
              (fkRectConfigurationToMedialPairing R omega)
            have h1 : f^[i] (f d) = f^[i + 1] d := by
              simpa only [Nat.succ_eq_add_one] using
                (Function.iterate_succ_apply f i d).symm
            have h2 : f^[i + 1] (f d) = f^[i + 2] d := by
              simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
                (Function.iterate_succ_apply f (i + 1) d).symm
            rw [h1, h2]
          rw [hshift]
          ac_rfl

theorem fkRectInsertedEdgeCharge_boundaryOrbitWalk
    (R : FKRectTorus) (omega : R.Configuration) (e : R.EdgeIndex)
    (d : FKMedialDart R.medialTorus) :
    fkRectInsertedEdgeCharge R e
        (fkRectMedialBoundaryPrimalOrbitWalk R omega d) =
      ∑ i ∈ Finset.range
          (orderOf (fkMedialBoundaryStep
            (fkRectConfigurationToMedialPairing R omega))),
        fkRectInsertedEdgeStepCharge R e
          (fkRectMedialDartPrimalLabel R
            ((fkMedialBoundaryStep
              (fkRectConfigurationToMedialPairing R omega))^[i] d))
          (fkRectMedialDartPrimalLabel R
            ((fkMedialBoundaryStep
              (fkRectConfigurationToMedialPairing R omega))^[i + 1] d)) := by
  unfold fkRectMedialBoundaryPrimalOrbitWalk
  rw [fkRectInsertedEdgeCharge_copy,
    fkRectInsertedEdgeCharge_boundaryTrace]

theorem fkRectInsertedEdgeStepCharge_black_eq_zero_of_ne
    (R : FKRectTorus) (omega : R.Configuration) (e : R.EdgeIndex)
    (d : FKMedialBlackDart R.medialTorus)
    (hd0 : d ≠ fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e))
    (hd1 : d ≠ fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e)) :
    fkRectInsertedEdgeStepCharge R e
        (fkRectMedialDartPrimalLabel R d.1)
        (fkRectMedialDartPrimalLabel R
          (fkMedialBoundaryStep
            (fkRectConfigurationToMedialPairing R omega) d.1)) = 0 := by
  let x := fkRectMedialDartPrimalLabel R d.1
  let y := fkRectMedialDartPrimalLabel R
    (fkMedialBoundaryStep
      (fkRectConfigurationToMedialPairing R omega) d.1)
  have hne : fkRectMedialWestPrimal R e ≠
      fkRectMedialEastPrimal R e := by
    intro h
    apply fkRectTorusIndexedEdge_ne_diag R e
      (fkRectMedialWestPrimal R e)
    simpa [h] using fkRectTorusIndexedEdge_eq_medialPrimals R e
  unfold fkRectInsertedEdgeStepCharge
  by_cases hforward : x = fkRectMedialWestPrimal R e ∧
      y = fkRectMedialEastPrimal R e
  · exfalso
    have hxy : x ≠ y := by
      rw [hforward.1, hforward.2]
      exact hne
    have hedge := (fkRectMedialBoundaryStep_label_eq_or_indexedEdge
      R omega d.1).resolve_left hxy
    have hv : d.1.1 = fkRectMedialVertexOfEdge R e := by
      apply (fkRectTorusMedialEdgeEquiv R).injective
      apply fkRectTorusIndexedEdge_injective R
      rw [hedge, fkRectTorusIndexedEdge_eq_medialPrimals]
      simp only [fkRectTorusMedialEdgeEquiv_vertexOfEdge]
      change s(x, y) = s(fkRectMedialWestPrimal R e,
        fkRectMedialEastPrimal R e)
      exact Sym2.eq_iff.mpr (Or.inl ⟨hforward.1, hforward.2⟩)
    rcases d with ⟨⟨v, side⟩, hd⟩
    simp only at hv
    subst v
    cases side <;> by_cases hp : fkMedialVertexParity
        (fkRectMedialVertexOfEdge R e) <;>
      simp [fkMedialBlackDart0, fkMedialBlackDart1,
        fkMedialCheckerColor, fkMedialSideVertical, hp] at hd hd0 hd1
  · rw [if_neg hforward]
    by_cases hreverse : x = fkRectMedialEastPrimal R e ∧
        y = fkRectMedialWestPrimal R e
    · exfalso
      have hxy : x ≠ y := by
        rw [hreverse.1, hreverse.2]
        exact hne.symm
      have hedge := (fkRectMedialBoundaryStep_label_eq_or_indexedEdge
        R omega d.1).resolve_left hxy
      have hv : d.1.1 = fkRectMedialVertexOfEdge R e := by
        apply (fkRectTorusMedialEdgeEquiv R).injective
        apply fkRectTorusIndexedEdge_injective R
        rw [hedge, fkRectTorusIndexedEdge_eq_medialPrimals]
        simp only [fkRectTorusMedialEdgeEquiv_vertexOfEdge]
        have hordered : s(x, y) = s(fkRectMedialEastPrimal R e,
            fkRectMedialWestPrimal R e) :=
          Sym2.eq_iff.mpr (Or.inl ⟨hreverse.1, hreverse.2⟩)
        exact hordered.trans Sym2.eq_swap
      rcases d with ⟨⟨v, side⟩, hd⟩
      simp only at hv
      subst v
      cases side <;> by_cases hp : fkMedialVertexParity
          (fkRectMedialVertexOfEdge R e) <;>
        simp [fkMedialBlackDart0, fkMedialBlackDart1,
          fkMedialCheckerColor, fkMedialSideVertical, hp] at hd hd0 hd1
    · rw [if_neg hreverse]

theorem fkRectInsertedEdgeStepCharge_new_dart0
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex) :
    fkRectInsertedEdgeStepCharge R e
        (fkRectMedialDartPrimalLabel R
          (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)).1)
        (fkRectMedialDartPrimalLabel R
          (fkMedialBoundaryStep
            (fkRectConfigurationToMedialPairing R
              (fkRectConfigurationOfEdges R (insert e F)))
            (fkMedialBlackDart0
              (fkRectMedialVertexOfEdge R e)).1)) =
      if fkMedialVertexParity (fkRectMedialVertexOfEdge R e) then 1 else -1 := by
  let v := fkRectMedialVertexOfEdge R e
  have hclosed : fkRectClosedPairingAtEdge e =
      !fkMedialVertexParity v := by
    have h := fkRectClosedMedialPairing_eq_not_vertexParity R v
    unfold fkRectClosedMedialPairing at h
    simpa [v] using h
  have hpair :
      fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R (insert e F)) v =
        fkMedialVertexParity v := by
    rw [fkRectConfigurationToMedialPairing_apply]
    rw [show fkRectTorusMedialEdgeEquiv R v = e by
      exact fkRectTorusMedialEdgeEquiv_vertexOfEdge R e]
    rw [show fkRectConfigurationOfEdges R (insert e F) e = true by
      simp [fkRectConfigurationOfEdges]]
    rw [hclosed]
    cases fkMedialVertexParity v <;> rfl
  have hne : fkRectMedialWestPrimal R e ≠
      fkRectMedialEastPrimal R e := by
    intro h
    apply fkRectTorusIndexedEdge_ne_diag R e
      (fkRectMedialWestPrimal R e)
    simpa [h] using fkRectTorusIndexedEdge_eq_medialPrimals R e
  rw [fkMedialBoundaryStep_apply,
    fkRectMedialDartPrimalLabel_bondMate]
  by_cases hp : fkMedialVertexParity v <;>
    simp [v, fkRectInsertedEdgeStepCharge, fkMedialBlackDart0,
      fkMedialLocalMate, hpair, fkRectMedialDartPrimalLabel,
      hclosed, hne,
      hp]

private theorem fkMedialBlackBoundaryPerm_iterate_val_charge
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (d : FKMedialBlackDart T) (n : Nat) :
    (((fkMedialBlackBoundaryPerm pairing)^[n] d).1) =
      (fkMedialBoundaryStep pairing)^[n] d.1 := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
      simp only [Function.iterate_succ_apply]
      rw [ih, fkMedialBlackBoundaryPerm_val_step]

private theorem perm_sameCycle_iterate
    {D : Type*} (sigma : Equiv.Perm D) (d : D) (n : Nat) :
    sigma.SameCycle d (sigma^[n] d) := by
  induction n with
  | zero => exact .rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ih.apply_right

theorem fkRectInsertedEdgeCharge_newBoundaryOrbit_ne_zero_of_reachable
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (hreach : (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
    fkRectInsertedEdgeCharge R e
      (fkRectMedialBoundaryPrimalOrbitWalk R
        (fkRectConfigurationOfEdges R (insert e F))
        (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)).1) ≠ 0 := by
  let oldPairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R F)
  let newPairing := fkRectConfigurationToMedialPairing R
    (fkRectConfigurationOfEdges R (insert e F))
  let v := fkRectMedialVertexOfEdge R e
  let a := fkMedialBlackDart0 v
  let b := fkMedialBlackDart1 v
  let tau := fkMedialBlackBoundaryPerm newPairing
  have holdab : (fkMedialBlackBoundaryPerm oldPairing).SameCycle a b := by
    apply (fkMedial_blackBoundary_sameCycle_iff_reachable oldPairing a b).2
    exact (fkMedialBlackDarts_reachable_iff_west_east oldPairing v).2 hreach
  have hnewab : ¬ tau.SameCycle a b := by
    change ¬ (fkMedialBlackBoundaryPerm newPairing).SameCycle a b
    rw [show newPairing = fkMedialTogglePairingAt oldPairing v by
      exact fkRectConfigurationToMedialPairing_insert R F e heF]
    rw [fkMedialBlackBoundaryPerm_toggle]
    exact StatMech.FrontierA.not_sameCycle_mul_swap_of_sameCycle
      (fkMedialBlackBoundaryPerm oldPairing)
      (fkMedialBlackDart0_ne_dart1 v) holdab
  rw [fkRectInsertedEdgeCharge_boundaryOrbitWalk]
  let parity := fkMedialVertexParity v
  let transform : Int → Int := fun z => if parity then z else -z
  intro hzero
  have htranszero : transform
      (∑ i ∈ Finset.range
        (orderOf (fkMedialBoundaryStep newPairing)),
          fkRectInsertedEdgeStepCharge R e
            (fkRectMedialDartPrimalLabel R
              ((fkMedialBoundaryStep newPairing)^[i] a.1))
            (fkRectMedialDartPrimalLabel R
              ((fkMedialBoundaryStep newPairing)^[i + 1] a.1))) = 0 := by
    rw [hzero]
    simp [transform]
  have hdistrib : transform
      (∑ i ∈ Finset.range
        (orderOf (fkMedialBoundaryStep newPairing)),
          fkRectInsertedEdgeStepCharge R e
            (fkRectMedialDartPrimalLabel R
              ((fkMedialBoundaryStep newPairing)^[i] a.1))
            (fkRectMedialDartPrimalLabel R
              ((fkMedialBoundaryStep newPairing)^[i + 1] a.1))) =
      ∑ i ∈ Finset.range
        (orderOf (fkMedialBoundaryStep newPairing)),
          transform (fkRectInsertedEdgeStepCharge R e
            (fkRectMedialDartPrimalLabel R
              ((fkMedialBoundaryStep newPairing)^[i] a.1))
            (fkRectMedialDartPrimalLabel R
              ((fkMedialBoundaryStep newPairing)^[i + 1] a.1))) := by
    by_cases hp : parity
    · simp [transform, hp]
    · simp [transform, hp, Finset.sum_neg_distrib]
  rw [hdistrib] at htranszero
  have hterm_nonneg (i : Nat) :
      0 ≤ transform (fkRectInsertedEdgeStepCharge R e
        (fkRectMedialDartPrimalLabel R
          ((fkMedialBoundaryStep newPairing)^[i] a.1))
        (fkRectMedialDartPrimalLabel R
          ((fkMedialBoundaryStep newPairing)^[i + 1] a.1))) := by
    let di : FKMedialBlackDart R.medialTorus := tau^[i] a
    have hval : di.1 = (fkMedialBoundaryStep newPairing)^[i] a.1 :=
      fkMedialBlackBoundaryPerm_iterate_val_charge newPairing a i
    have hvalnext : (tau di).1 =
        (fkMedialBoundaryStep newPairing)^[i + 1] a.1 := by
      rw [Function.iterate_succ_apply']
      change (tau (tau^[i] a)).1 = _
      rw [fkMedialBlackBoundaryPerm_val_step, hval]
    have hdib : di ≠ b := by
      intro hdib
      apply hnewab
      rw [← hdib]
      exact perm_sameCycle_iterate tau a i
    by_cases hdia : di = a
    · have hi : (fkMedialBoundaryStep newPairing)^[i] a.1 = a.1 := by
        rw [← hval, hdia]
      have hi1 : (fkMedialBoundaryStep newPairing)^[i + 1] a.1 =
          fkMedialBoundaryStep newPairing a.1 := by
        rw [Function.iterate_succ_apply', hi]
      rw [hi, hi1]
      rw [show newPairing = fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R (insert e F)) from rfl]
      rw [fkRectInsertedEdgeStepCharge_new_dart0]
      by_cases hp : parity <;> simp [transform, parity, v, hp] at *
    · have hi : (fkMedialBoundaryStep newPairing)^[i] a.1 = di.1 :=
        hval.symm
      have hi1 : (fkMedialBoundaryStep newPairing)^[i + 1] a.1 =
          fkMedialBoundaryStep newPairing di.1 := by
        rw [Function.iterate_succ_apply', hi]
      rw [hi, hi1]
      rw [fkRectInsertedEdgeStepCharge_black_eq_zero_of_ne
        R (fkRectConfigurationOfEdges R (insert e F)) e di hdia hdib]
      simp [transform]
  have hsumpos : 0 < ∑ i ∈ Finset.range
      (orderOf (fkMedialBoundaryStep newPairing)),
        transform (fkRectInsertedEdgeStepCharge R e
          (fkRectMedialDartPrimalLabel R
            ((fkMedialBoundaryStep newPairing)^[i] a.1))
          (fkRectMedialDartPrimalLabel R
            ((fkMedialBoundaryStep newPairing)^[i + 1] a.1))) := by
    apply Finset.sum_pos'
    · intro i hi
      exact hterm_nonneg i
    · refine ⟨0, Finset.mem_range.mpr (orderOf_pos _), ?_⟩
      simp only [Function.iterate_zero_apply, zero_add,
        Function.iterate_one]
      rw [show newPairing = fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R (insert e F)) from rfl]
      rw [fkRectInsertedEdgeStepCharge_new_dart0]
      by_cases hp : parity <;> simp [transform, parity, v, hp] at *
  rw [htranszero] at hsumpos
  exact (lt_irrefl 0) hsumpos

theorem fkRectConnectedInsertion_not_independent_of_reachable
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (heF : e ∉ F)
    (hold : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F))
    (hreach : (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (q : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialWestPrimal R e)) :
    ¬ FKRectWindingIndependent (fkRectWalkWinding R q)
      (fkRectWalkWinding R
        (fkRectInsertedFundamentalWalk R F e r)) := by
  intro hind
  let a := fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)
  let w := fkRectMedialBoundaryPrimalOrbitWalk R
    (fkRectConfigurationOfEdges R (insert e F)) a.1
  let z := fkRectInsertedFundamentalWalk R F e r
  have hcharge : fkRectInsertedEdgeCharge R e w ≠ 0 :=
    fkRectInsertedEdgeCharge_newBoundaryOrbit_ne_zero_of_reachable
      R F e heF hreach
  obtain ⟨qold, hdecomp⟩ := fkRectWalkWinding_insert_eq_old_add_charge
    R F e r heF w
  have hbase : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Reachable
        (fkRectMedialWestPrimal R e)
        (fkRectMedialDartPrimalLabel R a.1) := by
    have hclosed : fkRectClosedPairingAtEdge e =
        !fkMedialVertexParity (fkRectMedialVertexOfEdge R e) := by
      have h := fkRectClosedMedialPairing_eq_not_vertexParity R
        (fkRectMedialVertexOfEdge R e)
      unfold fkRectClosedMedialPairing at h
      simpa using h
    by_cases hp : fkMedialVertexParity (fkRectMedialVertexOfEdge R e)
    · have hlabel : fkRectMedialDartPrimalLabel R a.1 =
          fkRectMedialEastPrimal R e := by
        simp [a, fkMedialBlackDart0, fkRectMedialDartPrimalLabel,
          fkRectTorusMedialEdgeEquiv_vertexOfEdge,
          hclosed, hp]
      rw [hlabel]
      exact ⟨r⟩
    · have hlabel : fkRectMedialDartPrimalLabel R a.1 =
          fkRectMedialWestPrimal R e := by
        simp [a, fkMedialBlackDart0, fkRectMedialDartPrimalLabel,
          fkRectTorusMedialEdgeEquiv_vertexOfEdge,
          hclosed, hp]
      rw [hlabel]
  have hqold : ¬ FKRectWindingIndependent
      (fkRectWalkWinding R q) (fkRectWalkWinding R qold) := by
    intro hind
    apply hold
    exact FKRectHasNet.of_connected_closedWalks R
      (fkRectConfigurationOfEdges R F) hbase q qold hind
  have hwne : fkRectWalkWinding R w ≠ 0 := by
    intro hwzero
    unfold FKRectWindingIndependent at hind hqold
    push Not at hqold
    have hcoord := congrArg (fun t : Int × Int =>
      (fkRectWalkWinding R q).1 * t.2 -
        (fkRectWalkWinding R q).2 * t.1) hdecomp
    rw [hwzero] at hcoord
    simp only [Prod.fst_zero, Prod.snd_zero, zero_sub, neg_eq_zero,
      Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      zsmul_eq_mul, Prod.fst_mul, Prod.snd_mul, Prod.fst_intCast,
      Prod.snd_intCast, Int.cast_id] at hcoord
    have hmulneg : -(fkRectInsertedEdgeCharge R e w *
        ((fkRectWalkWinding R q).1 * (fkRectWalkWinding R z).2 -
          (fkRectWalkWinding R q).2 * (fkRectWalkWinding R z).1)) = 0 := by
      dsimp [z]
      linear_combination hcoord + hqold
    have hmul : fkRectInsertedEdgeCharge R e w *
        ((fkRectWalkWinding R q).1 * (fkRectWalkWinding R z).2 -
          (fkRectWalkWinding R q).2 * (fkRectWalkWinding R z).1) = 0 := by
      linarith
    have hn : fkRectInsertedEdgeCharge R e w = 0 :=
      (mul_eq_zero.mp hmul).resolve_right hind
    exact hcharge hn
  have hdepq : ¬ FKRectWindingIndependent
      (fkRectWalkWinding R w) (fkRectWalkWinding R q) := by
    have h := fkRect_boundaryOrbit_winding_dependent_of_openWalk
      R (insert e F) (q.mapLe (fkRectOpenGraph_le_insert R F e)) a.1
    rw [fkRectWalkWinding_mapLe] at h
    exact h
  have hqdep : ¬ FKRectWindingIndependent
      (fkRectWalkWinding R q) (fkRectWalkWinding R w) := by
    intro h
    exact hdepq ((fkRectWindingIndependent_comm _ _).mp h)
  have hdepf : ¬ FKRectWindingIndependent
      (fkRectWalkWinding R w) (fkRectWalkWinding R z) := by
    exact fkRect_boundaryOrbit_winding_dependent_of_openWalk
      R (insert e F) z a.1
  exact (not_windingIndependent_trans_of_middle_ne_zero
    (fkRectWalkWinding R q) (fkRectWalkWinding R w)
    (fkRectWalkWinding R z) hwne hqdep hdepf) hind



theorem fkRectConnectedInsertionSurfaceBridge_unconditional
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (heF : e ∉ F)
    (hold : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F)) :
    FKRectConnectedInsertionSurfaceBridge R F e r heF hold := by
  unfold FKRectConnectedInsertionSurfaceBridge
  constructor
  · intro hnotReachable
    let w := fkRectMedialBoundaryPrimalOrbitWalk R
      (fkRectConfigurationOfEdges R F)
      (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
    let q : (fkRectOpenGraph R
        (fkRectConfigurationOfEdges R F)).Walk
          (fkRectMedialWestPrimal R e) (fkRectMedialWestPrimal R e) :=
      w.copy
        (fkRectMedialDartPrimalLabel_west_vertexOfEdge R e)
        (fkRectMedialDartPrimalLabel_west_vertexOfEdge R e)
    refine ⟨q, ?_⟩
    rw [show fkRectWalkWinding R q = fkRectWalkWinding R w by
      exact fkRectWalkWinding_copy R w _ _]
    exact fkRectConnectedInsertion_boundary_windingIndependent_of_not_reachable
      R F e r heF hnotReachable
  · rintro ⟨q, hq⟩ hreachable
    exact (fkRectConnectedInsertion_not_independent_of_reachable
      R F e r heF hold hreachable q) hq

end
end StatMech.FrontierD
