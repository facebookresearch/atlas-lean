/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaComponentReflection
import Code.Sharpness.BackbonePartialEdgeCopySwitching
















open Finset

namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

local instance (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _



def lpReplicaCurrentEdgeReflect (G : SimpleGraph V) (sites : I -> V) :
    Equiv.Perm (lpReplicaCurrentGraph G sites).edgeFinset where
  toFun e := ⟨Sym2.map lpReplicaCurrentReflect e.1, by
    rcases e with ⟨e, he⟩
    induction e with
    | h x y =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      rw [SimpleGraph.mem_edgeFinset]
      change Sym2.map lpReplicaCurrentReflect s(x, y) ∈
        (lpReplicaCurrentGraph G sites).edgeSet
      rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
      exact (lpReplicaCurrentGraph_adj_reflect G sites x y).2 he⟩
  invFun e := ⟨Sym2.map lpReplicaCurrentReflect e.1, by
    rcases e with ⟨e, he⟩
    induction e with
    | h x y =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      rw [SimpleGraph.mem_edgeFinset]
      change Sym2.map lpReplicaCurrentReflect s(x, y) ∈
        (lpReplicaCurrentGraph G sites).edgeSet
      rw [Sym2.map_mk, SimpleGraph.mem_edgeSet]
      exact (lpReplicaCurrentGraph_adj_reflect G sites x y).2 he⟩
  left_inv := by
    intro e
    apply Subtype.ext
    change Sym2.map lpReplicaCurrentReflect
      (Sym2.map lpReplicaCurrentReflect e.1) = e.1
    rw [Sym2.map_map]
    have hf : (lpReplicaCurrentReflect : LPReplicaCurrentVertex V -> _)
        ∘ lpReplicaCurrentReflect = id := by
      funext x
      exact lpReplicaCurrentReflect_involutive x
    rw [hf, Sym2.map_id]
    rfl
  right_inv := by
    intro e
    apply Subtype.ext
    change Sym2.map lpReplicaCurrentReflect
      (Sym2.map lpReplicaCurrentReflect e.1) = e.1
    rw [Sym2.map_map]
    have hf : (lpReplicaCurrentReflect : LPReplicaCurrentVertex V -> _)
        ∘ lpReplicaCurrentReflect = id := by
      funext x
      exact lpReplicaCurrentReflect_involutive x
    rw [hf, Sym2.map_id]
    rfl

@[simp] theorem lpReplicaCurrentEdgeReflect_val
    (G : SimpleGraph V) (sites : I -> V)
    (e : (lpReplicaCurrentGraph G sites).edgeFinset) :
    (lpReplicaCurrentEdgeReflect G sites e).1 =
      Sym2.map lpReplicaCurrentReflect e.1 := rfl

theorem lpReplicaCurrentEdgeReflect_involutive
    (G : SimpleGraph V) (sites : I -> V) :
    Function.Involutive (lpReplicaCurrentEdgeReflect G sites) := by
  intro e
  apply Subtype.ext
  change Sym2.map lpReplicaCurrentReflect
    (Sym2.map lpReplicaCurrentReflect e.1) = e.1
  rw [Sym2.map_map]
  have hf : (lpReplicaCurrentReflect : LPReplicaCurrentVertex V -> _)
      ∘ lpReplicaCurrentReflect = id := by
    funext x
    exact lpReplicaCurrentReflect_involutive x
  rw [hf, Sym2.map_id]
  rfl



def lpReplicaReflectCopyEquiv
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) m ≃
      StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e)) where
  toFun c := ⟨lpReplicaCurrentEdgeReflect G sites c.1,
    ⟨c.2.val, by
      change c.2.val < m (lpReplicaCurrentEdgeReflect G sites
        (lpReplicaCurrentEdgeReflect G sites c.1))
      rw [lpReplicaCurrentEdgeReflect_involutive]
      exact c.2.isLt⟩⟩
  invFun c := ⟨lpReplicaCurrentEdgeReflect G sites c.1,
    ⟨c.2.val, by
      exact c.2.isLt⟩⟩
  left_inv := by
    rintro ⟨e, k⟩
    let he := lpReplicaCurrentEdgeReflect_involutive G sites e
    apply Sigma.ext he
    exact (Fin.heq_ext_iff (congrArg m he)).2 rfl
  right_inv := by
    rintro ⟨e, k⟩
    let he := lpReplicaCurrentEdgeReflect_involutive G sites e
    apply Sigma.ext he
    exact (Fin.heq_ext_iff (congrArg
      (fun x => m (lpReplicaCurrentEdgeReflect G sites x)) he)).2 rfl

theorem lpReplicaReflectCopyEquiv_ends
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) :
    StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites)
        (fun e => m (lpReplicaCurrentEdgeReflect G sites e))
        (lpReplicaReflectCopyEquiv G sites m c) =
      Sym2.map lpReplicaCurrentReflect
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) m c) := by
  rfl


def lpReplicaReflectCopies
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (S : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m)) :
    Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites)
        (fun e => m (lpReplicaCurrentEdgeReflect G sites e))) :=
  S.map (lpReplicaReflectCopyEquiv G sites m).toEmbedding

@[simp] theorem mem_lpReplicaReflectCopies
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (S : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites)
        (fun e => m (lpReplicaCurrentEdgeReflect G sites e))) :
    c ∈ lpReplicaReflectCopies G sites m S ↔
      (lpReplicaReflectCopyEquiv G sites m).symm c ∈ S := by
  simp [lpReplicaReflectCopies]

theorem lpReplicaReflectCopyEquiv_incident
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m)
    (x : LPReplicaCurrentVertex V) :
    lpReplicaCurrentReflect x ∈
        StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e))
          (lpReplicaReflectCopyEquiv G sites m c) ↔
      x ∈ StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) m c := by
  rw [lpReplicaReflectCopyEquiv_ends, Sym2.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have : y = x := lpReplicaCurrentReflect.injective hxy
    simpa [this] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem lpReplicaReflectCopies_degK
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (S : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (x : LPReplicaCurrentVertex V) :
    StatMech.Sharpness.RandomCurrent.degK
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
        (lpReplicaReflectCopies G sites m S)
        (lpReplicaCurrentReflect x) =
      StatMech.Sharpness.RandomCurrent.degK
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) m) S x := by
  unfold StatMech.Sharpness.RandomCurrent.degK lpReplicaReflectCopies
  rw [Finset.filter_map, Finset.card_map]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro c _
  exact lpReplicaReflectCopyEquiv_incident G sites m c x

theorem lpReplicaReflectCopies_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (S : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m)) :
    StatMech.Sharpness.RandomCurrent.sources
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
        (lpReplicaReflectCopies G sites m S) =
      (StatMech.Sharpness.RandomCurrent.sources
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) m) S).map
        lpReplicaCurrentReflect.toEmbedding := by
  ext y
  have hy := lpReplicaCurrentReflect_involutive (V := V) y
  rw [← hy]
  simp only [StatMech.Sharpness.RandomCurrent.mem_sources,
    lpReplicaReflectCopies_degK]
  simp

theorem lpReplicaReflectCopies_adjStep
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (S : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (a b : LPReplicaCurrentVertex V) :
    StatMech.Sharpness.RandomCurrent.adjStep
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
        (lpReplicaReflectCopies G sites m S)
        (lpReplicaCurrentReflect a) (lpReplicaCurrentReflect b) ↔
      StatMech.Sharpness.RandomCurrent.adjStep
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) m) S a b := by
  constructor
  · rintro ⟨c, hc, ha, hb, hab⟩
    let d := (lpReplicaReflectCopyEquiv G sites m).symm c
    have hdc : lpReplicaReflectCopyEquiv G sites m d = c :=
      (lpReplicaReflectCopyEquiv G sites m).apply_symm_apply c
    refine ⟨d, (mem_lpReplicaReflectCopies G sites m S c).1 hc, ?_, ?_, ?_⟩
    · rw [← hdc] at ha
      exact (lpReplicaReflectCopyEquiv_incident G sites m d a).1 ha
    · rw [← hdc] at hb
      exact (lpReplicaReflectCopyEquiv_incident G sites m d b).1 hb
    · exact fun h => hab (congrArg lpReplicaCurrentReflect h)
  · rintro ⟨c, hc, ha, hb, hab⟩
    refine ⟨lpReplicaReflectCopyEquiv G sites m c, ?_, ?_, ?_, ?_⟩
    · exact (mem_lpReplicaReflectCopies G sites m S _).2 (by simpa)
    · exact (lpReplicaReflectCopyEquiv_incident G sites m c a).2 ha
    · exact (lpReplicaReflectCopyEquiv_incident G sites m c b).2 hb
    · exact lpReplicaCurrentReflect.injective.ne hab

theorem lpReplicaReflectCopies_connK
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (S : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (a b : LPReplicaCurrentVertex V) :
    StatMech.Sharpness.RandomCurrent.connK
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
        (lpReplicaReflectCopies G sites m S)
        (lpReplicaCurrentReflect a) (lpReplicaCurrentReflect b) ↔
      StatMech.Sharpness.RandomCurrent.connK
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) m) S a b := by
  let e := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  let er := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites)
      (fun f => m (lpReplicaCurrentEdgeReflect G sites f))
  let R := lpReplicaReflectCopies G sites m S
  have hadj : ∀ x y,
      StatMech.Sharpness.RandomCurrent.adjStep er R x y ↔
        StatMech.Sharpness.RandomCurrent.adjStep e S
          (lpReplicaCurrentReflect x) (lpReplicaCurrentReflect y) := by
    intro x y
    have h := lpReplicaReflectCopies_adjStep G sites m S
      (lpReplicaCurrentReflect x) (lpReplicaCurrentReflect y)
    rw [lpReplicaCurrentReflect_involutive,
      lpReplicaCurrentReflect_involutive] at h
    exact h
  constructor
  · intro h
    have hmap : ∀ {x y},
        StatMech.Sharpness.RandomCurrent.connK er R x y ->
          StatMech.Sharpness.RandomCurrent.connK e S
            (lpReplicaCurrentReflect x) (lpReplicaCurrentReflect y) := by
      intro x y hxy
      induction hxy with
      | refl => exact Relation.ReflTransGen.refl
      | tail hxy hstep ih =>
          exact Relation.ReflTransGen.tail ih ((hadj _ _).1 hstep)
    have hh := hmap h
    rw [lpReplicaCurrentReflect_involutive,
      lpReplicaCurrentReflect_involutive] at hh
    exact hh
  · intro h
    have hmap : ∀ {x y},
        StatMech.Sharpness.RandomCurrent.connK e S x y ->
          StatMech.Sharpness.RandomCurrent.connK er R
            (lpReplicaCurrentReflect x) (lpReplicaCurrentReflect y) := by
      intro x y hxy
      induction hxy with
      | refl => exact Relation.ReflTransGen.refl
      | tail hxy hstep ih =>
          exact Relation.ReflTransGen.tail ih
            ((lpReplicaReflectCopies_adjStep G sites m S _ _).2 hstep)
    exact hmap h



def lpReplicaReflectedResidual (G : SimpleGraph V) (sites : I -> V)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (lpReplicaCurrentGraph G sites).edgeFinset -> Nat :=
  fun e => m (lpReplicaCurrentEdgeReflect G sites e) -
    a (lpReplicaCurrentEdgeReflect G sites e)



theorem lpReplicaCollision_projection
    (G : SimpleGraph V) (sites : I -> V)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) (ha : a <= m) :
    (fun e => a e + lpReplicaReflectedResidual G sites m a
      (lpReplicaCurrentEdgeReflect G sites e)) = m := by
  funext e
  rw [lpReplicaReflectedResidual, lpReplicaCurrentEdgeReflect_involutive]
  exact Nat.add_sub_cancel' (ha e)



def lpReplicaCollisionProfile (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (lpReplicaCurrentGraph G sites).edgeFinset -> Nat :=
  fun e => a e + b (lpReplicaCurrentEdgeReflect G sites e)




abbrev LPReplicaCollisionCopy
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  Σ e : (lpReplicaCurrentGraph G sites).edgeFinset,
    Fin (a e) ⊕ Fin (b (lpReplicaCurrentEdgeReflect G sites e))



def lpReplicaCollisionCopyEquiv
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaCollisionCopy G sites a b ≃
      StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites a b) :=
  Equiv.sigmaCongrRight (fun _ => finSumFinEquiv)

@[simp] theorem lpReplicaCollisionCopyEquiv_edge
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : LPReplicaCollisionCopy G sites a b) :
    (lpReplicaCollisionCopyEquiv G sites a b c).1 = c.1 := rfl

theorem lpReplicaCollisionCopyEquiv_ends
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : LPReplicaCollisionCopy G sites a b) :
    StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites a b)
        (lpReplicaCollisionCopyEquiv G sites a b c) = c.1.1 := by
  rfl


def lpReplicaCollisionLeftCopyEmbedding
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) a ↪
      StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites a b) :=
  ({
    toFun := fun c => ⟨c.1, Sum.inl c.2⟩
    inj' := by
      rintro ⟨e, k⟩ ⟨f, l⟩ h
      cases h
      rfl
  } : StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) a ↪
      LPReplicaCollisionCopy G sites a b).trans
    (lpReplicaCollisionCopyEquiv G sites a b).toEmbedding


def lpReplicaCollisionRightCopyEmbedding
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) b ↪
      StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites a b) :=
  (lpReplicaReflectCopyEquiv G sites b).toEmbedding |>.trans
    (({
      toFun := fun c => ⟨c.1, Sum.inr c.2⟩
      inj' := by
        rintro ⟨e, k⟩ ⟨f, l⟩ h
        cases h
        rfl
    } : StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites)
            (fun e => b (lpReplicaCurrentEdgeReflect G sites e)) ↪
        LPReplicaCollisionCopy G sites a b).trans
        (lpReplicaCollisionCopyEquiv G sites a b).toEmbedding)

theorem lpReplicaCollisionLeftCopyEmbedding_ends
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) a) :
    StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites a b)
        (lpReplicaCollisionLeftCopyEmbedding G sites a b c) =
      StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) a c := by
  rcases c with ⟨e, k⟩
  simp [lpReplicaCollisionLeftCopyEmbedding,
    StatMech.Sharpness.FluxEdgeCopy.endsM,
    lpReplicaCollisionCopyEquiv]

theorem lpReplicaCollisionRightCopyEmbedding_ends
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) b) :
    StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites a b)
        (lpReplicaCollisionRightCopyEmbedding G sites a b c) =
      Sym2.map lpReplicaCurrentReflect
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) b c) := by
  rcases c with ⟨e, k⟩
  simp [lpReplicaCollisionRightCopyEmbedding,
    StatMech.Sharpness.FluxEdgeCopy.endsM,
    lpReplicaCollisionCopyEquiv,
    lpReplicaReflectCopyEquiv]

theorem randomCurrent_sources_map_embedding
    {K L W : Type*} [Fintype W] [DecidableEq W]
    (endsK : K -> Sym2 W) (endsL : L -> Sym2 W)
    (f : K ↪ L) (hends : ∀ c, endsL (f c) = endsK c)
    (S : Finset K) :
    StatMech.Sharpness.RandomCurrent.sources endsL (S.map f) =
      StatMech.Sharpness.RandomCurrent.sources endsK S := by
  classical
  ext x
  simp only [StatMech.Sharpness.RandomCurrent.sources,
    Finset.mem_filter, Finset.mem_univ, true_and]
  unfold StatMech.Sharpness.RandomCurrent.degK
  rw [Finset.filter_map, Finset.card_map]
  have hfilter :
      S.filter ((fun i => x ∈ endsL i) ∘ f) =
        S.filter (fun i => x ∈ endsK i) := by
    apply Finset.filter_congr
    intro c _
    change x ∈ endsL (f c) ↔ x ∈ endsK c
    rw [hends c]
  rw [hfilter]

theorem randomCurrent_connK_map_embedding
    {K L W : Type*}
    (endsK : K -> Sym2 W) (endsL : L -> Sym2 W)
    (f : K ↪ L) (hends : ∀ c, endsL (f c) = endsK c)
    (S : Finset K) (u v : W) :
    StatMech.Sharpness.RandomCurrent.connK endsL (S.map f) u v ↔
      StatMech.Sharpness.RandomCurrent.connK endsK S u v := by
  classical
  have hadj : ∀ x y,
      StatMech.Sharpness.RandomCurrent.adjStep endsL (S.map f) x y ↔
        StatMech.Sharpness.RandomCurrent.adjStep endsK S x y := by
    intro x y
    constructor
    · rintro ⟨c, hc, hx, hy, hxy⟩
      simp only [Finset.mem_map] at hc
      rcases hc with ⟨d, hd, rfl⟩
      exact ⟨d, hd, hends d ▸ hx, hends d ▸ hy, hxy⟩
    · rintro ⟨c, hc, hx, hy, hxy⟩
      exact ⟨f c, Finset.mem_map.mpr ⟨c, hc, rfl⟩,
        hends c ▸ hx, hends c ▸ hy, hxy⟩
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail h hstep ih =>
        exact Relation.ReflTransGen.tail ih ((hadj _ _).1 hstep)
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail h hstep ih =>
        exact Relation.ReflTransGen.tail ih ((hadj _ _).2 hstep)


def lpReplicaReflectProfileEquiv
    (G : SimpleGraph V) (sites : I -> V) :
    ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) ≃
      ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) where
  toFun b := fun e => b (lpReplicaCurrentEdgeReflect G sites e)
  invFun b := fun e => b (lpReplicaCurrentEdgeReflect G sites e)
  left_inv := by
    intro b
    funext e
    dsimp only
    rw [lpReplicaCurrentEdgeReflect_involutive]
  right_inv := by
    intro b
    funext e
    dsimp only
    rw [lpReplicaCurrentEdgeReflect_involutive]




def lpReplicaPairEquivCollisionSigma
    (G : SimpleGraph V) (sites : I -> V) :
    (((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) ×
      ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat)) ≃
      (Σ m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat,
        {a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat // a <= m}) :=
  (Equiv.prodCongr (Equiv.refl _)
    (lpReplicaReflectProfileEquiv G sites)).trans
      (StatMech.Sharpness.pairEquivSigma
        (E := (lpReplicaCurrentGraph G sites).edgeFinset))

@[simp] theorem lpReplicaPairEquivCollisionSigma_apply_fst
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (lpReplicaPairEquivCollisionSigma G sites (a, b)).1 =
      lpReplicaCollisionProfile G sites a b := rfl

@[simp] theorem lpReplicaPairEquivCollisionSigma_apply_subprofile
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    (lpReplicaPairEquivCollisionSigma G sites (a, b)).2.1 = a := rfl

open StatMech.Sharpness



theorem lpReplicaWeight_reflect
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    weight (lpReplicaCurrentGraph G sites) beta
        (lpReplicaCurrentCoupling J hf r)
        (ofEdgeFun (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e))) =
      weight (lpReplicaCurrentGraph G sites) beta
        (lpReplicaCurrentCoupling J hf r)
        (ofEdgeFun (lpReplicaCurrentGraph G sites) m) := by
  rw [weight_ofEdgeFun, weight_ofEdgeFun]
  apply Fintype.prod_equiv (lpReplicaCurrentEdgeReflect G sites)
  intro e
  simp only [lpReplicaCurrentEdgeReflect_val]
  rw [lpReplicaCurrentCoupling_reflect]

theorem lpReplicaReflectedResidual_weight
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (m a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    weight (lpReplicaCurrentGraph G sites) beta
        (lpReplicaCurrentCoupling J hf r)
        (ofEdgeFun (lpReplicaCurrentGraph G sites)
          (lpReplicaReflectedResidual G sites m a)) =
      weight (lpReplicaCurrentGraph G sites) beta
        (lpReplicaCurrentCoupling J hf r)
        (ofEdgeFun (lpReplicaCurrentGraph G sites)
          (fun e => m e - a e)) := by
  exact lpReplicaWeight_reflect G sites beta J hf r
    (fun e => m e - a e)




def lpReplicaCollisionPredicateFiberMass
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Q : ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) ->
      ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) -> Prop)
    [DecidablePred (fun a => Q a
      (lpReplicaReflectedResidual G sites m a))] : Real :=
  ∑ K : {a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat // a <= m},
    if Q K.1 (lpReplicaReflectedResidual G sites m K.1) then
      weight (lpReplicaCurrentGraph G sites) beta
          (lpReplicaCurrentCoupling J hf r)
          (ofEdgeFun (lpReplicaCurrentGraph G sites) K.1) *
        weight (lpReplicaCurrentGraph G sites) beta
          (lpReplicaCurrentCoupling J hf r)
          (ofEdgeFun (lpReplicaCurrentGraph G sites)
            (lpReplicaReflectedResidual G sites m K.1))
    else 0




theorem lpReplicaCollisionPredicateFiberMass_eq_edgecopy
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Q : ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) ->
      ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) -> Prop)
    [DecidablePred (fun a => Q a
      (lpReplicaReflectedResidual G sites m a))] :
    lpReplicaCollisionPredicateFiberMass G sites beta J hf r m Q =
      ∑ S : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) m),
        if Q
            (StatMech.Sharpness.FluxEdgeCopy.profileFlux
              (lpReplicaCurrentGraph G sites) m S)
            (lpReplicaReflectedResidual G sites m
              (StatMech.Sharpness.FluxEdgeCopy.profileFlux
                (lpReplicaCurrentGraph G sites) m S)) then
          weight (lpReplicaCurrentGraph G sites) beta
            (lpReplicaCurrentCoupling J hf r)
            (ofEdgeFun (lpReplicaCurrentGraph G sites) m)
        else 0 := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let Jr := lpReplicaCurrentCoupling J hf r
  let W : Real := weight H beta Jr (ofEdgeFun H m)
  let R : (H.edgeFinset -> Nat) -> Prop := fun a =>
    Q a (lpReplicaReflectedResidual G sites m a)
  have hterm : ∀ K : {a : H.edgeFinset -> Nat // a <= m},
      (if R K.1 then
          weight H beta Jr (ofEdgeFun H K.1) *
            weight H beta Jr
              (ofEdgeFun H (lpReplicaReflectedResidual G sites m K.1))
        else 0) =
      (∏ e : H.edgeFinset, (m e).choose (K.1 e)) •
        (if R K.1 then W else 0) := by
    intro K
    by_cases hR : R K.1
    · rw [if_pos hR, if_pos hR]
      rw [lpReplicaReflectedResidual_weight
        G sites beta J hf r m K.1]
      rw [weight_split_eq_binom H beta Jr m K.1 K.2]
      rw [nsmul_eq_mul, Nat.cast_prod]
      congr 1
      rw [← Finset.prod_attach H.edgeFinset]
      apply Finset.prod_congr rfl
      intro e _
      simp only [ofEdgeFun]
      rw [dif_pos e.2, dif_pos e.2]
    · simp [hR]
  unfold lpReplicaCollisionPredicateFiberMass
  change (∑ K : {a : H.edgeFinset -> Nat // a <= m},
      if R K.1 then
        weight H beta Jr (ofEdgeFun H K.1) *
          weight H beta Jr
            (ofEdgeFun H (lpReplicaReflectedResidual G sites m K.1))
      else 0) = _
  rw [show (∑ K : {a : H.edgeFinset -> Nat // a <= m},
      if R K.1 then
        weight H beta Jr (ofEdgeFun H K.1) *
          weight H beta Jr
            (ofEdgeFun H (lpReplicaReflectedResidual G sites m K.1))
      else 0) = ∑ K : {a : H.edgeFinset -> Nat // a <= m},
        (∏ e : H.edgeFinset, (m e).choose (K.1 e)) •
          (if R K.1 then W else 0) by
    apply Finset.sum_congr rfl
    intro K _
    exact hterm K]
  rw [StatMech.Sharpness.FluxEdgeCopy.flux_edgecopy_bridge H m
    (fun a => if R a then W else 0)]




theorem lpReplicaCollision_tsum_mul
    (G : SimpleGraph V) (sites : I -> V)
    (f g : ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) -> Real)
    (hf : Summable (fun a => ‖f a‖))
    (hg : Summable (fun b => ‖g b‖)) :
    (∑' a, f a) * (∑' b, g b) =
      ∑' m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat,
        ∑ K : {a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat // a <= m},
          f K.1 * g (lpReplicaReflectedResidual G sites m K.1) := by
  let E := (lpReplicaCurrentGraph G sites).edgeFinset
  let Q := lpReplicaPairEquivCollisionSigma G sites
  have hfg : Summable (fun z : (E -> Nat) × (E -> Nat) =>
      f z.1 * g z.2) :=
    summable_mul_of_summable_norm hf hg
  let F : (Σ m : E -> Nat, {a : E -> Nat // a <= m}) -> Real :=
    fun s => f s.2.1 * g (lpReplicaReflectedResidual G sites s.1 s.2.1)
  have hcomp : ∀ z : (E -> Nat) × (E -> Nat),
      f z.1 * g z.2 = F (Q z) := by
    rintro ⟨a, b⟩
    change f a * g b = f a * g (fun e =>
      (a (lpReplicaCurrentEdgeReflect G sites e) +
          b (lpReplicaCurrentEdgeReflect G sites
            (lpReplicaCurrentEdgeReflect G sites e))) -
        a (lpReplicaCurrentEdgeReflect G sites e))
    congr 2
    funext e
    rw [lpReplicaCurrentEdgeReflect_involutive]
    exact (Nat.add_sub_cancel_left
      (a (lpReplicaCurrentEdgeReflect G sites e)) (b e)).symm
  have hsumF : Summable F := by
    rw [← Q.summable_iff]
    exact hfg.congr hcomp
  rw [show (∑' a, f a) * (∑' b, g b) =
      ∑' z : (E -> Nat) × (E -> Nat), f z.1 * g z.2 by
    exact Summable.tsum_mul_tsum hf.of_norm hg.of_norm hfg]
  rw [tsum_congr hcomp, Q.tsum_eq F, Summable.tsum_sigma hsumF]
  apply tsum_congr
  intro m
  rw [tsum_fintype]



def lpReplicaCollisionObservableFiberMass
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Theta : ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) ->
      ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) -> Real) : Real :=
  ∑ K : {a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat // a <= m},
    Theta K.1 (lpReplicaReflectedResidual G sites m K.1) *
      (weight (lpReplicaCurrentGraph G sites) beta
          (lpReplicaCurrentCoupling J hf r)
          (ofEdgeFun (lpReplicaCurrentGraph G sites) K.1) *
        weight (lpReplicaCurrentGraph G sites) beta
          (lpReplicaCurrentCoupling J hf r)
          (ofEdgeFun (lpReplicaCurrentGraph G sites)
            (lpReplicaReflectedResidual G sites m K.1)))



theorem lpReplicaCollisionObservableFiberMass_eq_edgecopy
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Theta : ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) ->
      ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) -> Real) :
    lpReplicaCollisionObservableFiberMass
        G sites beta J hf r m Theta =
      ∑ S : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) m),
        Theta
            (StatMech.Sharpness.FluxEdgeCopy.profileFlux
              (lpReplicaCurrentGraph G sites) m S)
            (lpReplicaReflectedResidual G sites m
              (StatMech.Sharpness.FluxEdgeCopy.profileFlux
                (lpReplicaCurrentGraph G sites) m S)) *
          weight (lpReplicaCurrentGraph G sites) beta
            (lpReplicaCurrentCoupling J hf r)
            (ofEdgeFun (lpReplicaCurrentGraph G sites) m) := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let Jr := lpReplicaCurrentCoupling J hf r
  let W : Real := weight H beta Jr (ofEdgeFun H m)
  have hterm : ∀ K : {a : H.edgeFinset -> Nat // a <= m},
      Theta K.1 (lpReplicaReflectedResidual G sites m K.1) *
          (weight H beta Jr (ofEdgeFun H K.1) *
            weight H beta Jr
              (ofEdgeFun H (lpReplicaReflectedResidual G sites m K.1))) =
        (∏ e : H.edgeFinset, (m e).choose (K.1 e)) •
          (Theta K.1 (lpReplicaReflectedResidual G sites m K.1) * W) := by
    intro K
    rw [lpReplicaReflectedResidual_weight G sites beta J hf r m K.1]
    rw [weight_split_eq_binom H beta Jr m K.1 K.2]
    rw [nsmul_eq_mul, Nat.cast_prod]
    have hprod :
        (∏ e ∈ H.edgeFinset,
            (Nat.choose ((ofEdgeFun H m) e)
              ((ofEdgeFun H K.1) e) : Real)) =
          ∏ e : H.edgeFinset, ((m e).choose (K.1 e) : Real) := by
      rw [← Finset.prod_attach H.edgeFinset]
      apply Finset.prod_congr rfl
      intro e _
      simp only [ofEdgeFun]
      rw [dif_pos e.2, dif_pos e.2]
    rw [hprod]
    ring
  unfold lpReplicaCollisionObservableFiberMass
  change (∑ K : {a : H.edgeFinset -> Nat // a <= m},
    Theta K.1 (lpReplicaReflectedResidual G sites m K.1) *
      (weight H beta Jr (ofEdgeFun H K.1) *
        weight H beta Jr
          (ofEdgeFun H (lpReplicaReflectedResidual G sites m K.1)))) = _
  rw [show (∑ K : {a : H.edgeFinset -> Nat // a <= m},
      Theta K.1 (lpReplicaReflectedResidual G sites m K.1) *
        (weight H beta Jr (ofEdgeFun H K.1) *
          weight H beta Jr
            (ofEdgeFun H (lpReplicaReflectedResidual G sites m K.1)))) =
      ∑ K : {a : H.edgeFinset -> Nat // a <= m},
        (∏ e : H.edgeFinset, (m e).choose (K.1 e)) •
          (Theta K.1 (lpReplicaReflectedResidual G sites m K.1) * W) by
    apply Finset.sum_congr rfl
    intro K _
    exact hterm K]
  rw [StatMech.Sharpness.FluxEdgeCopy.flux_edgecopy_bridge H m
    (fun a => Theta a (lpReplicaReflectedResidual G sites m a) * W)]


def lpReplicaCollisionFiberMass
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) : Real :=
  ∑ K : {a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat // a <= m},
    weight (lpReplicaCurrentGraph G sites) beta
        (lpReplicaCurrentCoupling J hf r)
        (ofEdgeFun (lpReplicaCurrentGraph G sites) K.1) *
      weight (lpReplicaCurrentGraph G sites) beta
        (lpReplicaCurrentCoupling J hf r)
        (ofEdgeFun (lpReplicaCurrentGraph G sites)
          (lpReplicaReflectedResidual G sites m K.1))




theorem lpReplicaCollisionFiberMass_eq
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaCollisionFiberMass G sites beta J hf r m =
      (2 : Real) ^ (∑ e, m e) *
        weight (lpReplicaCurrentGraph G sites) beta
          (lpReplicaCurrentCoupling J hf r)
          (ofEdgeFun (lpReplicaCurrentGraph G sites) m) := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let Jr := lpReplicaCurrentCoupling J hf r
  let W : Real := weight H beta Jr (ofEdgeFun H m)
  have hterm : ∀ K : {a : H.edgeFinset -> Nat // a <= m},
      weight H beta Jr (ofEdgeFun H K.1) *
          weight H beta Jr
            (ofEdgeFun H (lpReplicaReflectedResidual G sites m K.1)) =
        (∏ e : H.edgeFinset, (m e).choose (K.1 e)) • W := by
    intro K
    rw [lpReplicaReflectedResidual_weight G sites beta J hf r m K.1]
    rw [weight_split_eq_binom H beta Jr m K.1 K.2]
    rw [nsmul_eq_mul, Nat.cast_prod]
    congr 1
    rw [← Finset.prod_attach H.edgeFinset]
    apply Finset.prod_congr rfl
    intro e _
    simp only [ofEdgeFun]
    rw [dif_pos e.2, dif_pos e.2]
  unfold lpReplicaCollisionFiberMass
  change (∑ K : {a : H.edgeFinset -> Nat // a <= m},
      weight H beta Jr (ofEdgeFun H K.1) *
        weight H beta Jr
          (ofEdgeFun H (lpReplicaReflectedResidual G sites m K.1))) = _
  rw [show (∑ K : {a : H.edgeFinset -> Nat // a <= m},
      weight H beta Jr (ofEdgeFun H K.1) *
        weight H beta Jr
          (ofEdgeFun H (lpReplicaReflectedResidual G sites m K.1))) =
      ∑ K : {a : H.edgeFinset -> Nat // a <= m},
        (∏ e : H.edgeFinset, (m e).choose (K.1 e)) • W by
    apply Finset.sum_congr rfl
    intro K _
    exact hterm K]
  rw [StatMech.Sharpness.FluxEdgeCopy.flux_edgecopy_bridge H m
    (fun _ => W)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp [W, H, Jr, Fintype.card_sigma]

end

end StatMech.Ising
