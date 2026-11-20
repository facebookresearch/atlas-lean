/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Sharpness.Claim1IsingComplete
import Code.Sharpness.MeanfieldIsingMass
import Code.Sharpness.TildeBc









open Finset SimpleGraph

namespace StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]



theorem couplingIn_nested {J : Sym2 V -> Real} {S T : Finset V}
    (hST : S ⊆ T) :
    couplingIn (couplingIn J T) S = couplingIn J S := by
  funext e
  unfold couplingIn
  by_cases hS : edgeInside S e
  · have hT : edgeInside T e := fun x hx => hST (hS x hx)
    simp [hS, hT]
  · simp [hS]


theorem expectationJ_couplingIn_mono_domain
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    {S T : Finset V} (hST : S ⊆ T) (A : Finset V) :
    expectationJ G beta (couplingIn J S) A <=
      expectationJ G beta (couplingIn J T) A := by
  have hJT : forall e, 0 <= couplingIn J T e := by
    intro e
    unfold couplingIn
    split <;> simp_all [hJ e]
  have h := expectationJ_couplingIn_le G beta (couplingIn J T)
    hbeta hJT S A
  rwa [couplingIn_nested hST] at h

open StatMech.Lattice



theorem freeCorr_mono_domain {d : Nat} {beta : Real}
    (hbeta : 0 <= beta) {S T : Finset (Site d)} (hST : S ⊆ T)
    {a b : Site d} (haS : a ∈ S) (hbS : b ∈ S) :
    freeCorr d beta S ⟨a, haS⟩ ⟨b, hbS⟩ <=
      freeCorr d beta T ⟨a, hST haS⟩ ⟨b, hST hbS⟩ := by
  classical
  by_cases hab : a = b
  · subst b
    simp
  let aT : {x // x ∈ T} := ⟨a, hST haS⟩
  let bT : {x // x ∈ T} := ⟨b, hST hbS⟩
  let ST : Finset {x // x ∈ T} :=
    T.attach.filter (fun x => x.1 ∈ S)
  have mem_ST (x : {x // x ∈ T}) : x ∈ ST ↔ x.1 ∈ S := by
    simp [ST]
  have haST : aT ∈ ST := (mem_ST aT).2 haS
  have hbST : bT ∈ ST := (mem_ST bT).2 hbS
  let aSmall : {x // x ∈ ST} := ⟨aT, haST⟩
  let bSmall : {x // x ∈ ST} := ⟨bT, hbST⟩
  let sigma : {x // x ∈ ST} ≃ {x // x ∈ S} :=
    { toFun := fun x => ⟨x.1.1, (mem_ST x.1).1 x.2⟩
      invFun := fun x =>
        ⟨⟨x.1, hST x.2⟩, (mem_ST ⟨x.1, hST x.2⟩).2 x.2⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro x
        apply Subtype.ext
        rfl }
  have hsigma : forall x y,
      ((graphS d T).comap
        (Subtype.val : {x // x ∈ ST} -> {x // x ∈ T})).Adj x y ↔
        (graphS d S).Adj (sigma x) (sigma y) := by
    intro x y
    rfl
  have hmap : ({aSmall, bSmall} : Finset {x // x ∈ ST}).map
      sigma.toEmbedding =
        ({⟨a, haS⟩, ⟨b, hbS⟩} : Finset {x // x ∈ S}) := by
    ext x
    simp [aSmall, bSmall, aT, bT, sigma]
  have hlocalized := expectationJ_couplingIn_one_eq_induced
    (graphS d T) beta ST haST hbST
  have hmono := expectationJ_couplingIn_le
    (graphS d T) beta (fun _ => 1) hbeta (fun _ => by norm_num)
      ST ({aT, bT} : Finset {x // x ∈ T})
  rw [expectationJ_one_eq_isingExpectation] at hmono
  rw [hlocalized] at hmono
  have hrel := StatMech.Ising.isingExpectation_spinProd_relabel
    ((graphS d T).comap
      (Subtype.val : {x // x ∈ ST} -> {x // x ∈ T}))
    (graphS d S) sigma hsigma beta 0
    ({aSmall, bSmall} : Finset {x // x ∈ ST})
  rw [hmap] at hrel
  rw [hrel] at hmono
  simpa [freeCorr, aT, bT, aSmall, bSmall, hab] using hmono

end StatMech.Sharpness
