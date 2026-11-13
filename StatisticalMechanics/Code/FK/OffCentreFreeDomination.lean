/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.OffCentreDomination











open scoped BigOperators
open SimpleGraph

namespace StatMech.FK

noncomputable section



theorem bcProb_congr_boundary {V : Type*} [Fintype V] [DecidableEq V]
    (G C D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel C.Adj] [DecidableRel D.Adj]
    (h : C = D) (p q : Real) (omega : ConfigSpace (Sym2 V)) :
    bcProb G C p q omega = bcProb G D p q omega := by
  subst D
  congr 1

variable {Vin Vout : Type*}
variable [Fintype Vin] [DecidableEq Vin]
variable [Fintype Vout] [DecidableEq Vout]
variable (Gin : SimpleGraph Vin) [DecidableRel Gin.Adj]
variable (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]
variable (iota : Vin -> Vout)

private def falseBoundary (_ : Vout) : Prop := False

private instance : DecidablePred (falseBoundary : Vout -> Prop) :=
  fun _ => isFalse id

private theorem boundaryClique_false_eq_bot :
    StatMech.Lattice.boundaryCliqueGraph
        (falseBoundary : Vout -> Prop) =
      (⊥ : SimpleGraph Vout) := by
  apply SimpleGraph.ext
  funext x y
  apply propext
  rw [StatMech.Lattice.boundaryCliqueGraph_adj]
  simp [falseBoundary, SimpleGraph.bot_adj]

private theorem bcProb_falseBoundary_eq_fkProb
    (G : SimpleGraph Vout) [DecidableRel G.Adj]
    (p q : Real) (omega : ConfigSpace (Sym2 Vout)) :
    bcProb G
        (StatMech.Lattice.boundaryCliqueGraph
          (falseBoundary : Vout -> Prop)) p q omega =
      fkProb G p q omega := by
  simpa only [boundaryClique_false_eq_bot] using
    (bcProb_bot_eq_fkProb G p q omega)



theorem ocd_condFreeProb_innerRestrict_ge
    (hiota : Function.Injective iota)
    (hadj : ocd_AdjMatch Gin Gout iota)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (psi : ConfigSpace (Sym2 Vout))
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsIncreasing A) :
    (∑ rho,
        (ocd_innerRestrict iota ⁻¹' A).indicator (fun _ => (1 : Real)) rho *
          condBcProb Gout
            (StatMech.Lattice.boundaryCliqueGraph
              (falseBoundary : Vout -> Prop))
            p q (ocd_innerEdgeFinset (Vin := Vin) iota) psi rho) >=
      ∑ omega,
        A.indicator (fun _ => (1 : Real)) omega * fkProb Gin p q omega := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  rw [ocd_condBcProb_psiExt_sum_eq_inducedBox
    (bdryOut := (falseBoundary : Vout -> Prop))
    hiota hadj hp hp1 hq0 psi (ocd_innerRestrict iota ⁻¹' A)]
  have hpre : ocd_psiExt iota psi ⁻¹'
      (ocd_innerRestrict iota ⁻¹' A) = A := by
    ext omega
    simp only [Set.mem_preimage, ocd_innerRestrict_psiExt hiota]
  rw [hpre]
  have hmono := bcProb_free_le Gin
    (ocd_inducedWiring Gout iota
      (falseBoundary : Vout -> Prop) psi)
    hp hp1 hq hA
  simpa only [bcProb_bot_eq_fkProb] using hmono





theorem ocd_free_inner_le_outer_fkProb
    (hiota : Function.Injective iota)
    (hadj : ocd_AdjMatch Gin Gout iota)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsIncreasing A) :
    (∑ omega,
        A.indicator (fun _ => (1 : Real)) omega * fkProb Gin p q omega) <=
      ∑ rho,
        (ocd_innerRestrict iota ⁻¹' A).indicator (fun _ => (1 : Real)) rho *
          fkProb Gout p q rho := by
  let c := ∑ omega,
    A.indicator (fun _ => (1 : Real)) omega * fkProb Gin p q omega
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  rw [show (∑ rho,
      (ocd_innerRestrict iota ⁻¹' A).indicator (fun _ => (1 : Real)) rho *
        fkProb Gout p q rho) =
      ∑ rho,
        (ocd_innerRestrict iota ⁻¹' A).indicator (fun _ => (1 : Real)) rho *
          bcProb Gout
            (StatMech.Lattice.boundaryCliqueGraph
              (falseBoundary : Vout -> Prop)) p q rho by
    apply Finset.sum_congr rfl
    intro rho _
    rw [bcProb_falseBoundary_eq_fkProb]]
  rw [ocd_bcProb_decompose
    (bdryOut := (falseBoundary : Vout -> Prop))
    hiota hp hp1 hq0 (ocd_innerRestrict iota ⁻¹' A)]
  have hsum :
      (∑ psi ∈ Finset.univ.filter
          (fun psi => ocd_outProj iota psi = psi),
        ∑ sigma ∈ condFibre
          (ocd_innerEdgeFinset (Vin := Vin) iota) psi,
            bcProb Gout
              (StatMech.Lattice.boundaryCliqueGraph
                (falseBoundary : Vout -> Prop)) p q sigma) = 1 :=
    ocd_sum_fibreMass_eq_one
      (Gout := Gout) (bdryOut := (falseBoundary : Vout -> Prop))
      hiota hp hp1 hq0
  calc
    c = (∑ psi ∈ Finset.univ.filter
          (fun psi => ocd_outProj iota psi = psi),
        (∑ sigma ∈ condFibre
          (ocd_innerEdgeFinset (Vin := Vin) iota) psi,
            bcProb Gout
              (StatMech.Lattice.boundaryCliqueGraph
                (falseBoundary : Vout -> Prop)) p q sigma)) * c := by
      rw [hsum, one_mul]
    _ = ∑ psi ∈ Finset.univ.filter
          (fun psi => ocd_outProj iota psi = psi),
        (∑ sigma ∈ condFibre
          (ocd_innerEdgeFinset (Vin := Vin) iota) psi,
            bcProb Gout
              (StatMech.Lattice.boundaryCliqueGraph
                (falseBoundary : Vout -> Prop)) p q sigma) * c := by
      rw [Finset.sum_mul]
    _ <= ∑ psi ∈ Finset.univ.filter
          (fun psi => ocd_outProj iota psi = psi),
        (∑ sigma ∈ condFibre
          (ocd_innerEdgeFinset (Vin := Vin) iota) psi,
            bcProb Gout
              (StatMech.Lattice.boundaryCliqueGraph
                (falseBoundary : Vout -> Prop)) p q sigma) *
          (∑ rho,
            (ocd_innerRestrict iota ⁻¹' A).indicator
                (fun _ => (1 : Real)) rho *
              condBcProb Gout
                (StatMech.Lattice.boundaryCliqueGraph
                  (falseBoundary : Vout -> Prop)) p q
                (ocd_innerEdgeFinset (Vin := Vin) iota) psi rho) := by
      apply Finset.sum_le_sum
      intro psi hpsi
      apply mul_le_mul_of_nonneg_left
      . exact ocd_condFreeProb_innerRestrict_ge Gin Gout iota
          hiota hadj hp hp1 hq psi hA
      . exact Finset.sum_nonneg fun sigma _ =>
          bcProb_nonneg Gout
            (StatMech.Lattice.boundaryCliqueGraph
              (falseBoundary : Vout -> Prop)) hp hp1 hq0 sigma

end

end StatMech.FK
