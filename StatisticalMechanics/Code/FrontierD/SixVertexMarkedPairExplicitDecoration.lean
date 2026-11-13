/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexMarkedPairCTypeHall










open Finset

namespace StatMech.FrontierD

noncomputable section

local instance instDecidablePropExplicitDecoration (p : Prop) : Decidable p :=
  Classical.propDecidable p


abbrev MarkedBinaryDecoration (Site : Type*) [Fintype Site]
    [DecidableEq Site] (k : Nat) :=
  Sigma fun marked : {s : Finset Site // s.card = k} =>
    ({site : Site // site ∉ marked.1} -> Bool)

theorem card_complement_subtype
    {Site : Type*} [Fintype Site] [DecidableEq Site]
    (marked : Finset Site) :
    Fintype.card {site : Site // site ∉ marked} =
      Fintype.card Site - marked.card := by
  rw [Fintype.card_subtype_compl]
  congr 1
  rw [Fintype.card_subtype]
  simp

theorem card_marked_finsets
    (Site : Type*) [Fintype Site] [DecidableEq Site] (k : Nat) :
    Fintype.card {s : Finset Site // s.card = k} =
      (Fintype.card Site).choose k := by
  rw [Fintype.card_subtype]
  rw [show (Finset.univ.filter fun s : Finset Site => s.card = k) =
      Finset.univ.powersetCard k by
    ext s
    simp]
  rw [Finset.card_powersetCard]
  simp

theorem card_markedBinaryDecoration
    (Site : Type*) [Fintype Site] [DecidableEq Site] (k : Nat) :
    Fintype.card (MarkedBinaryDecoration Site k) =
      2 ^ (Fintype.card Site - k) * (Fintype.card Site).choose k := by
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_fun, Fintype.card_bool,
    card_complement_subtype]
  have hcard (marked : {s : Finset Site // s.card = k}) :
      Fintype.card Site - marked.1.card = Fintype.card Site - k := by
    rw [marked.2]
  simp_rw [hcard]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    card_marked_finsets]
  exact Nat.mul_comm _ _


abbrev SixVertexPairCTypeSite
    {T : EvenTorus} (omega eta : SixVertexArrows T) :=
  {x : Bool × T.Vertex //
    (if x.1 then eta else omega).IsCType x.2}

def sixVertexPairCTypeSiteEquivSum
    {T : EvenTorus} (omega eta : SixVertexArrows T) :
    SixVertexPairCTypeSite omega eta ≃
      {v : T.Vertex // omega.IsCType v} ⊕
        {v : T.Vertex // eta.IsCType v} where
  toFun x := if h : x.1.1 = false then
      Sum.inl ⟨x.1.2, by simpa [h] using x.2⟩
    else Sum.inr ⟨x.1.2, by
      have ht : x.1.1 = true := Bool.eq_true_of_not_eq_false h
      simpa [ht] using x.2⟩
  invFun x := match x with
    | Sum.inl v => ⟨(false, v.1), by simpa using v.2⟩
    | Sum.inr v => ⟨(true, v.1), by simpa using v.2⟩
  left_inv x := by
    rcases x with ⟨⟨layer, v⟩, hc⟩
    cases layer <;> simp
  right_inv x := by
    rcases x with v | v <;> simp

theorem card_cTypeSite
    {T : EvenTorus} (omega : SixVertexArrows T) :
    Fintype.card {v : T.Vertex // omega.IsCType v} =
      sixVertexTorusCTypeCount omega := by
  rw [Fintype.card_subtype]
  unfold sixVertexTorusCTypeCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem card_sixVertexPairCTypeSite
    {T : EvenTorus} (omega eta : SixVertexArrows T) :
    Fintype.card (SixVertexPairCTypeSite omega eta) =
      sixVertexTorusCTypeCount omega + sixVertexTorusCTypeCount eta := by
  rw [Fintype.card_congr
      (sixVertexPairCTypeSiteEquivSum omega eta),
    Fintype.card_sum, card_cTypeSite, card_cTypeSite]

theorem fkLoopPairingCompatible_of_cType
    {T : EvenTorus} (omega : SixVertexArrows T)
    (homega : omega.IceRule) (v : T.Vertex)
    (hc : omega.IsCType v) (pairing : Bool) :
    fkLoopPairingCompatible pairing omega v := by
  have hi := homega v
  generalize hw : omega.horizontal
    (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) = w at hi hc ⊢
  generalize he : omega.horizontal v = e at hi hc ⊢
  generalize hs : omega.vertical
    (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) = s at hi hc ⊢
  generalize hn : omega.vertical v = n at hi hc ⊢
  cases pairing <;> cases w <;> cases e <;> cases s <;> cases n <;>
    simp [fkLoopPairingCompatible, SixVertexArrows.IsCType,
      SixVertexArrows.incomingCount, fkLoopWestIncoming,
      fkLoopEastIncoming, fkLoopSouthIncoming, fkLoopNorthIncoming,
      hw, he, hs, hn] at hi hc ⊢


def sixVertexPreferredCompatiblePairing
    {T : EvenTorus} (omega : SixVertexArrows T) (v : T.Vertex) : Bool :=
  if fkLoopPairingCompatible false omega v then false else true

theorem sixVertexPreferredCompatiblePairing_compatible
    {T : EvenTorus} (omega : SixVertexArrows T)
    (homega : omega.IceRule) (v : T.Vertex) :
    fkLoopPairingCompatible
      (sixVertexPreferredCompatiblePairing omega v) omega v := by
  unfold sixVertexPreferredCompatiblePairing
  split
  · assumption
  · rename_i hfalse
    have hi := homega v
    generalize hw : omega.horizontal
      (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) = w at hi hfalse ⊢
    generalize he : omega.horizontal v = e at hi hfalse ⊢
    generalize hs : omega.vertical
      (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) = s at hi hfalse ⊢
    generalize hn : omega.vertical v = n at hi hfalse ⊢
    cases w <;> cases e <;> cases s <;> cases n <;>
      simp [fkLoopPairingCompatible, SixVertexArrows.incomingCount,
        fkLoopWestIncoming, fkLoopEastIncoming,
        fkLoopSouthIncoming, fkLoopNorthIncoming,
        hw, he, hs, hn] at hi hfalse ⊢


abbrev SixVertexExplicitMarkedPairDecoration
    {T : EvenTorus} (omega eta : SixVertexArrows T) (k : Nat) :=
  MarkedBinaryDecoration (SixVertexPairCTypeSite omega eta) k


def sixVertexArrowPairLayer
    {T : EvenTorus} (omega eta : SixVertexArrows T) (layer : Bool) :
    SixVertexArrows T :=
  if layer then eta else omega




noncomputable def sixVertexExplicitMarkedPartialPairing
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k)
    (layer : Bool) (v : T.Vertex) : Option Bool :=
  let arrows := sixVertexArrowPairLayer omega eta layer
  if hc : arrows.IsCType v then
    let site : SixVertexPairCTypeSite omega eta :=
      ⟨(layer, v), by simpa [arrows, sixVertexArrowPairLayer] using hc⟩
    if hm : site ∈ decoration.1.1 then none
    else some (decoration.2 ⟨site, hm⟩)
  else some (sixVertexPreferredCompatiblePairing arrows v)

theorem sixVertexExplicitMarkedPartialPairing_eq_none_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k)
    (layer : Bool) (v : T.Vertex) :
    sixVertexExplicitMarkedPartialPairing decoration layer v =
        none ↔
      ∃ site ∈ decoration.1.1, site.1 = (layer, v) := by
  dsimp only [sixVertexExplicitMarkedPartialPairing]
  split
  · rename_i hc
    let site : SixVertexPairCTypeSite omega eta :=
      ⟨(layer, v), by
        simpa [sixVertexArrowPairLayer] using hc⟩
    split
    · rename_i hm
      constructor
      · intro h
        exact ⟨site, hm, rfl⟩
      · intro h
        rfl
    · rename_i hm
      constructor
      · intro h
        contradiction
      · rintro ⟨other, hother, hval⟩
        exfalso
        apply hm
        have heq : other = site := Subtype.ext hval
        simpa [heq] using hother
  · rename_i hc
    constructor
    · intro h
      contradiction
    · rintro ⟨site, hsite, hval⟩
      exfalso
      apply hc
      simpa [sixVertexArrowPairLayer, hval] using site.2


def sixVertexExplicitMarkedSiteProjection
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k) :
    Finset (Bool × T.Vertex) :=
  decoration.1.1.map (Function.Embedding.subtype _)

theorem mem_sixVertexExplicitMarkedSiteProjection_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k)
    (layer : Bool) (v : T.Vertex) :
    (layer, v) ∈ sixVertexExplicitMarkedSiteProjection decoration ↔
      ∃ site ∈ decoration.1.1, site.1 = (layer, v) := by
  simp [sixVertexExplicitMarkedSiteProjection]


def sixVertexExplicitUnresolvedSiteFinset
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k) :
    Finset (Bool × T.Vertex) :=
  Finset.univ.filter fun x =>
    sixVertexExplicitMarkedPartialPairing decoration x.1 x.2 = none

theorem sixVertexExplicitUnresolvedSiteFinset_eq_projection
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k) :
    sixVertexExplicitUnresolvedSiteFinset decoration =
      sixVertexExplicitMarkedSiteProjection decoration := by
  ext x
  rcases x with ⟨layer, v⟩
  simp [sixVertexExplicitUnresolvedSiteFinset,
    mem_sixVertexExplicitMarkedSiteProjection_iff,
    sixVertexExplicitMarkedPartialPairing_eq_none_iff]

theorem card_sixVertexExplicitUnresolvedSiteFinset
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k) :
    (sixVertexExplicitUnresolvedSiteFinset decoration).card = k := by
  rw [sixVertexExplicitUnresolvedSiteFinset_eq_projection]
  simp [sixVertexExplicitMarkedSiteProjection, decoration.1.2]


abbrev SixVertexExplicitMarkedResolution
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k) :=
  ({x : Bool × T.Vertex //
      x ∈ sixVertexExplicitUnresolvedSiteFinset decoration} -> Bool)

theorem card_sixVertexExplicitMarkedResolution
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k) :
    Fintype.card (SixVertexExplicitMarkedResolution decoration) = 2 ^ k := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe,
    card_sixVertexExplicitUnresolvedSiteFinset]



noncomputable def sixVertexExplicitMarkedResolutionEquivFin
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k) :
    SixVertexExplicitMarkedResolution decoration ≃ Fin (2 ^ k) := by
  apply Fintype.equivOfCardEq
  rw [Fintype.card_fin, card_sixVertexExplicitMarkedResolution]


noncomputable def sixVertexExplicitResolvedPairing
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k)
    (resolution : SixVertexExplicitMarkedResolution decoration)
    (layer : Bool) (v : T.Vertex) : Bool :=
  if hnone : sixVertexExplicitMarkedPartialPairing decoration layer v = none
  then resolution ⟨(layer, v), by
    simp [sixVertexExplicitUnresolvedSiteFinset, hnone]⟩
  else
    (sixVertexExplicitMarkedPartialPairing decoration layer v).get
      (Option.isSome_iff_ne_none.mpr hnone)

theorem sixVertexExplicitResolvedPairing_eq_of_partial_eq_some
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k)
    (resolution : SixVertexExplicitMarkedResolution decoration)
    (layer : Bool) (v : T.Vertex) (pairing : Bool)
    (hpairing : sixVertexExplicitMarkedPartialPairing
      decoration layer v = some pairing) :
    sixVertexExplicitResolvedPairing decoration resolution layer v =
      pairing := by
  simp [sixVertexExplicitResolvedPairing, hpairing]

theorem sixVertexExplicitResolvedPairing_eq_resolution
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k)
    (resolution : SixVertexExplicitMarkedResolution decoration)
    (site : {x : Bool × T.Vertex //
      x ∈ sixVertexExplicitUnresolvedSiteFinset decoration}) :
    sixVertexExplicitResolvedPairing decoration resolution
        site.1.1 site.1.2 = resolution site := by
  have hnone : sixVertexExplicitMarkedPartialPairing decoration
      site.1.1 site.1.2 = none := by
    simpa only [sixVertexExplicitUnresolvedSiteFinset,
      Finset.mem_filter, Finset.mem_univ, true_and] using site.2
  simp [sixVertexExplicitResolvedPairing, hnone]

theorem sixVertexExplicitMarkedPartialPairing_compatible
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k)
    (layer : Bool) (v : T.Vertex) (pairing : Bool)
    (hpairing : sixVertexExplicitMarkedPartialPairing
      decoration layer v = some pairing) :
    fkLoopPairingCompatible pairing
      (sixVertexArrowPairLayer omega eta layer) v := by
  dsimp only [sixVertexExplicitMarkedPartialPairing] at hpairing
  split at hpairing
  · rename_i hc
    split at hpairing
    · simp at hpairing
    ·
      apply fkLoopPairingCompatible_of_cType
      · cases layer
        · exact homega
        · exact heta
      · exact hc
  · rename_i hc
    have hp : pairing = sixVertexPreferredCompatiblePairing
        (sixVertexArrowPairLayer omega eta layer) v := by
      simpa using hpairing.symm
    subst pairing
    apply sixVertexPreferredCompatiblePairing_compatible
    cases layer
    · exact homega
    · exact heta

theorem sixVertexExplicitResolvedPairing_compatible
    {T : EvenTorus} {omega eta : SixVertexArrows T} {k : Nat}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (decoration : SixVertexExplicitMarkedPairDecoration omega eta k)
    (resolution : SixVertexExplicitMarkedResolution decoration)
    (layer : Bool) (v : T.Vertex) :
    fkLoopPairingCompatible
      (sixVertexExplicitResolvedPairing decoration resolution layer v)
      (sixVertexArrowPairLayer omega eta layer) v := by
  by_cases hnone : sixVertexExplicitMarkedPartialPairing
      decoration layer v = none
  · apply fkLoopPairingCompatible_of_cType
    · cases layer
      · exact homega
      · exact heta
    · obtain ⟨site, hsite, hval⟩ :=
        (sixVertexExplicitMarkedPartialPairing_eq_none_iff
          decoration layer v).mp hnone
      simpa [sixVertexArrowPairLayer, hval] using site.2
  · obtain ⟨pairing, hpairing⟩ :=
      Option.ne_none_iff_exists'.mp hnone
    rw [sixVertexExplicitResolvedPairing_eq_of_partial_eq_some
      decoration resolution layer v pairing hpairing]
    exact sixVertexExplicitMarkedPartialPairing_compatible
      homega heta decoration layer v pairing hpairing

theorem card_sixVertexExplicitMarkedPairDecoration
    {T : EvenTorus} (omega eta : SixVertexArrows T) (k : Nat) :
    Fintype.card (SixVertexExplicitMarkedPairDecoration omega eta k) =
      sixVertexMarkedPairMultiplicityNat omega eta k := by
  rw [card_markedBinaryDecoration, card_sixVertexPairCTypeSite]
  rfl



noncomputable def sixVertexExplicitMarkedPairDecorationEquivFin
    {T : EvenTorus} (omega eta : SixVertexArrows T) (k : Nat) :
    SixVertexExplicitMarkedPairDecoration omega eta k ≃
      Fin (sixVertexMarkedPairMultiplicityNat omega eta k) := by
  apply Fintype.equivOfCardEq
  rw [Fintype.card_fin,
    card_sixVertexExplicitMarkedPairDecoration]


abbrev SixVertexExplicitMarkedDecoratedPair
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat) :=
  Sigma fun pair : SixVertexMarkedSectorConfiguration T left ×
      SixVertexMarkedSectorConfiguration T right =>
    SixVertexExplicitMarkedPairDecoration pair.1.1 pair.2.1 k


noncomputable def sixVertexExplicitMarkedDecoratedPairEquiv
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat) :
    SixVertexExplicitMarkedDecoratedPair T left right k ≃
      SixVertexMarkedDecoratedPair T left right k :=
  Equiv.sigmaCongrRight fun pair =>
    sixVertexExplicitMarkedPairDecorationEquivFin
      pair.1.1 pair.2.1 k

end

end StatMech.FrontierD
