/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectTorusRandomCluster
import Code.Foundations.FiniteNonnegativeMatrixRate
import Code.Lattice.EulerFaces2










open Finset Matrix Filter Topology

namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable




def finiteBoundaryConnectivityGraph {V B : Type*} (G : SimpleGraph V)
    (embed : B -> V) : SimpleGraph B where
  Adj u v := u ≠ v ∧ G.Reachable (embed u) (embed v)
  symm := by
    rintro u v ⟨huv, hreach⟩
    exact ⟨huv.symm, hreach.symm⟩
  loopless := ⟨by simp⟩

theorem finiteBoundaryConnectivityGraph_reachable_iff
    {V B : Type*} (G : SimpleGraph V) (embed : B -> V) (u v : B) :
    (finiteBoundaryConnectivityGraph G embed).Reachable u v ↔
      G.Reachable (embed u) (embed v) := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons hadj p ih => exact hadj.2.trans ih
  · intro hreach
    by_cases huv : u = v
    · subst v
      exact SimpleGraph.Reachable.refl _
    · exact (show (finiteBoundaryConnectivityGraph G embed).Adj u v from
        ⟨huv, hreach⟩).reachable



noncomputable def finiteBoundaryComponentEquiv
    {V B : Type*} (G : SimpleGraph V) (embed : B -> V) :
    (finiteBoundaryConnectivityGraph G embed).ConnectedComponent ≃
      {C : G.ConnectedComponent //
        ∃ u : B, G.connectedComponentMk (embed u) = C} := by
  let K := finiteBoundaryConnectivityGraph G embed
  let toAmbient : K.ConnectedComponent -> G.ConnectedComponent :=
    Quot.lift (fun u : B => G.connectedComponentMk (embed u))
      (fun u v huv => SimpleGraph.ConnectedComponent.sound
        ((finiteBoundaryConnectivityGraph_reachable_iff G embed u v).1 huv))
  refine
    { toFun := fun C => ⟨toAmbient C, ?_⟩
      invFun := fun C => K.connectedComponentMk (Classical.choose C.2)
      left_inv := ?_
      right_inv := ?_ }
  · refine SimpleGraph.ConnectedComponent.ind (G := K) (fun u => ?_) C
    exact ⟨u, rfl⟩
  · intro C
    refine SimpleGraph.ConnectedComponent.ind (G := K) (fun u => ?_) C
    apply SimpleGraph.ConnectedComponent.sound
    apply (finiteBoundaryConnectivityGraph_reachable_iff G embed _ _).2
    apply SimpleGraph.ConnectedComponent.exact
    exact Classical.choose_spec (show
      ∃ b : B, G.connectedComponentMk (embed b) =
        G.connectedComponentMk (embed u) from ⟨u, rfl⟩)
  · rintro ⟨C, hC⟩
    apply Subtype.ext
    dsimp only
    exact Classical.choose_spec hC



theorem finite_component_count_eq_closed_add_boundary
    {V B : Type*} [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B]
    (G : SimpleGraph V) (embed : B -> V) :
    Fintype.card G.ConnectedComponent =
      (Finset.univ.filter fun C : G.ConnectedComponent =>
        ∀ u : B, G.connectedComponentMk (embed u) ≠ C).card +
      Fintype.card
        (finiteBoundaryConnectivityGraph G embed).ConnectedComponent := by
  classical
  let p : G.ConnectedComponent -> Prop := fun C =>
    ∃ u : B, G.connectedComponentMk (embed u) = C
  have hmeet : Fintype.card
      (finiteBoundaryConnectivityGraph G embed).ConnectedComponent =
      Fintype.card {C : G.ConnectedComponent // p C} :=
    Fintype.card_congr (finiteBoundaryComponentEquiv G embed)
  have hclosed :
      (Finset.univ.filter fun C : G.ConnectedComponent =>
        ∀ u : B, G.connectedComponentMk (embed u) ≠ C).card =
      Fintype.card {C : G.ConnectedComponent // ¬p C} := by
    rw [Fintype.card_subtype]
    congr 1
    ext C
    simp [p]
  rw [hclosed, hmeet, Fintype.card_subtype_compl]
  exact (Nat.sub_add_cancel (Fintype.card_subtype_le p)).symm





def finiteBoundaryEdgeRun {V B : Type*} (embed : B -> V) :
    SimpleGraph V -> List (B × B) -> SimpleGraph V
  | G, [] => G
  | G, e :: edges =>
      finiteBoundaryEdgeRun embed (G ⊔ SimpleGraph.edge (embed e.1) (embed e.2)) edges

theorem finiteBoundaryEdgeRun_adj_iff
    {V B : Type*} (embed : B -> V) (G : SimpleGraph V)
    (edges : List (B × B)) (u v : V) :
    (finiteBoundaryEdgeRun embed G edges).Adj u v ↔
      G.Adj u v ∨ ∃ e ∈ edges,
        (SimpleGraph.edge (embed e.1) (embed e.2)).Adj u v := by
  induction edges generalizing G with
  | nil => simp [finiteBoundaryEdgeRun]
  | cons e edges ih =>
      rw [finiteBoundaryEdgeRun, ih]
      simp only [SimpleGraph.sup_adj, List.mem_cons]
      aesop

theorem finiteBoundaryEdgeRun_reachable_iff
    {V B : Type*} (embed : B -> V) (G : SimpleGraph V) (K : SimpleGraph B)
    (hreach : ∀ x y, G.Reachable (embed x) (embed y) ↔ K.Reachable x y)
    (edges : List (B × B)) (x y : B) :
    (finiteBoundaryEdgeRun embed G edges).Reachable (embed x) (embed y) ↔
      (finiteBoundaryEdgeRun id K edges).Reachable x y := by
  induction edges generalizing G K with
  | nil => exact hreach x y
  | cons e edges ih =>
      apply ih
      intro u v
      rw [StatMech.Lattice.reachable_sup_edge,
        StatMech.Lattice.reachable_sup_edge]
      simp only [hreach, id_eq]




theorem finiteBoundaryEdgeRun_component_cross_sum
    {V B : Type*} [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq B]
    (embed : B -> V) (G : SimpleGraph V) (K : SimpleGraph B)
    (hreach : ∀ x y, G.Reachable (embed x) (embed y) ↔ K.Reachable x y)
    (edges : List (B × B)) :
    Nat.card G.ConnectedComponent +
        Nat.card (finiteBoundaryEdgeRun id K edges).ConnectedComponent =
      Nat.card K.ConnectedComponent +
        Nat.card (finiteBoundaryEdgeRun embed G edges).ConnectedComponent := by
  induction edges generalizing G K with
  | nil => simp [finiteBoundaryEdgeRun, Nat.add_comm]
  | cons e edges ih =>
      let G' := G ⊔ SimpleGraph.edge (embed e.1) (embed e.2)
      let K' := K ⊔ SimpleGraph.edge e.1 e.2
      have hreach' : ∀ x y,
          G'.Reachable (embed x) (embed y) ↔ K'.Reachable x y := by
        intro x y
        dsimp only [G', K']
        rw [StatMech.Lattice.reachable_sup_edge,
          StatMech.Lattice.reachable_sup_edge]
        simp only [hreach, id_eq]
      have hind := ih G' K' hreach'
      simp only [finiteBoundaryEdgeRun] at hind ⊢
      by_cases hk : K.Reachable e.1 e.2
      · have hg : G.Reachable (embed e.1) (embed e.2) :=
          (hreach e.1 e.2).2 hk
        have hG := StatMech.Lattice.card_components_sup_edge_of_reachable
          G (embed e.1) (embed e.2) hg
        have hK := StatMech.Lattice.card_components_sup_edge_of_reachable
          K e.1 e.2 hk
        dsimp only [G', K'] at hind
        simp only [id_eq] at hind
        rw [hG, hK] at hind
        exact hind
      · have hg : ¬G.Reachable (embed e.1) (embed e.2) := by
          exact fun h => hk ((hreach e.1 e.2).1 h)
        have hG := StatMech.Lattice.card_components_sup_edge_of_not_reachable
          G (embed e.1) (embed e.2) hg
        have hK := StatMech.Lattice.card_components_sup_edge_of_not_reachable
          K e.1 e.2 hk
        dsimp only [G', K'] at hind
        calc
          Nat.card G.ConnectedComponent +
                Nat.card (finiteBoundaryEdgeRun id K (e :: edges)).ConnectedComponent =
              (Nat.card (G ⊔ SimpleGraph.edge (embed e.1) (embed e.2)).ConnectedComponent + 1) +
                Nat.card (finiteBoundaryEdgeRun id K (e :: edges)).ConnectedComponent := by
                  rw [hG]
          _ = (Nat.card (G ⊔ SimpleGraph.edge (embed e.1) (embed e.2)).ConnectedComponent +
                Nat.card (finiteBoundaryEdgeRun id
                  (K ⊔ SimpleGraph.edge e.1 e.2) edges).ConnectedComponent) + 1 := by
                  simp only [finiteBoundaryEdgeRun, id_eq]
                  ac_rfl
          _ = (Nat.card (K ⊔ SimpleGraph.edge e.1 e.2).ConnectedComponent +
                Nat.card (finiteBoundaryEdgeRun embed
                  (G ⊔ SimpleGraph.edge (embed e.1) (embed e.2)) edges).ConnectedComponent) + 1 := by
                  rw [hind]
          _ = Nat.card K.ConnectedComponent +
                Nat.card (finiteBoundaryEdgeRun embed G (e :: edges)).ConnectedComponent := by
                  simp only [finiteBoundaryEdgeRun]
                  omega




abbrev FKRectBoundaryState (W : Nat) := SimpleGraph (Bool × Fin W)

noncomputable instance fkRectBoundaryStateDecidableEq (W : Nat) :
    DecidableEq (FKRectBoundaryState W) := Classical.decEq _



def FKRectBoundaryState.IsConnectivity {W : Nat}
    (state : FKRectBoundaryState W) : Prop :=
  ∀ u v, state.Adj u v ↔ u ≠ v ∧ state.Reachable u v


abbrev FKRectBoundaryConnectivityState (W : Nat) :=
  {state : FKRectBoundaryState W // state.IsConnectivity}

noncomputable instance fkRectBoundaryConnectivityStateDecidableEq (W : Nat) :
    DecidableEq (FKRectBoundaryConnectivityState W) := Classical.decEq _





def fkRectConfigurationLayer (R : FKRectTorus) (omega : R.Configuration)
    (y : Fin R.height) : Bool × Fin R.width -> Bool :=
  fun a => omega (a.1, (a.2, y))



def fkRectConfigurationLayersEquiv (R : FKRectTorus) :
    R.Configuration ≃ (Fin R.height -> Bool × Fin R.width -> Bool) where
  toFun omega y a := omega (a.1, (a.2, y))
  invFun layers a := layers a.2.2 (a.1, a.2.1)
  left_inv omega := by
    funext a
    rfl
  right_inv layers := by
    funext y a
    rfl

@[simp] theorem fkRectConfigurationLayersEquiv_apply
    (R : FKRectTorus) (omega : R.Configuration) (y : Fin R.height) :
    fkRectConfigurationLayersEquiv R omega y =
      fkRectConfigurationLayer R omega y := rfl


abbrev FKRectLayerVertex (W : Nat) := Fin 3 × Fin W

def fkRectLayerInitialRole : Fin 3 := ⟨0, by omega⟩
def fkRectLayerOldRole : Fin 3 := ⟨1, by omega⟩
def fkRectLayerNewRole : Fin 3 := ⟨2, by omega⟩


def fkRectLayerInputEmbed {W : Nat} (u : Bool × Fin W) :
    FKRectLayerVertex W :=
  (if u.1 then fkRectLayerOldRole else fkRectLayerInitialRole, u.2)


def fkRectLayerOutputEmbed {W : Nat} (u : Bool × Fin W) :
    FKRectLayerVertex W :=
  (if u.1 then fkRectLayerNewRole else fkRectLayerInitialRole, u.2)

theorem fkRectLayerInputEmbed_injective {W : Nat} :
    Function.Injective (fkRectLayerInputEmbed :
      Bool × Fin W -> FKRectLayerVertex W) := by
  rintro ⟨b, x⟩ ⟨b', x'⟩ h
  cases b <;> cases b' <;> simp [fkRectLayerInputEmbed,
    fkRectLayerInitialRole, fkRectLayerOldRole] at h ⊢
  all_goals exact h

theorem fkRectLayerOutputEmbed_injective {W : Nat} :
    Function.Injective (fkRectLayerOutputEmbed :
      Bool × Fin W -> FKRectLayerVertex W) := by
  rintro ⟨b, x⟩ ⟨b', x'⟩ h
  cases b <;> cases b' <;> simp [fkRectLayerOutputEmbed,
    fkRectLayerInitialRole, fkRectLayerNewRole] at h ⊢
  all_goals exact h



def fkRectLayerEdgeEndpoints {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (a : Bool × Fin W) : FKRectLayerVertex W × FKRectLayerVertex W :=
  if a.1 then
    ((fkRectLayerOldRole, a.2), (fkRectLayerNewRole, a.2))
  else if evenRow then
    ((fkRectLayerOldRole, SixVertexArrows.cyclicPred hW a.2),
      (fkRectLayerNewRole, a.2))
  else
    ((fkRectLayerOldRole, a.2),
      (fkRectLayerNewRole, SixVertexArrows.cyclicPred hW a.2))

theorem fkRectLayerEdgeEndpoints_ne {W : Nat} (hW : 0 < W)
    (evenRow : Bool) (a : Bool × Fin W) :
    (fkRectLayerEdgeEndpoints hW evenRow a).1 ≠
      (fkRectLayerEdgeEndpoints hW evenRow a).2 := by
  cases a with
  | mk dir x =>
      cases dir <;> cases evenRow <;>
        simp [fkRectLayerEdgeEndpoints, fkRectLayerOldRole,
          fkRectLayerNewRole]



def fkRectBoundaryLayerGraph {W : Nat} (hW : 0 < W)
    (evenRow : Bool) (state : FKRectBoundaryState W)
    (eta : Bool × Fin W -> Bool) : SimpleGraph (FKRectLayerVertex W) where
  Adj u v :=
    (∃ x y, state.Adj x y ∧ fkRectLayerInputEmbed x = u ∧
      fkRectLayerInputEmbed y = v) ∨
    ∃ a, eta a = true ∧
      (((fkRectLayerEdgeEndpoints hW evenRow a).1 = u ∧
          (fkRectLayerEdgeEndpoints hW evenRow a).2 = v) ∨
        ((fkRectLayerEdgeEndpoints hW evenRow a).1 = v ∧
          (fkRectLayerEdgeEndpoints hW evenRow a).2 = u))
  symm := by
    rintro u v (hstate | hedge)
    · obtain ⟨x, y, hxy, rfl, rfl⟩ := hstate
      exact Or.inl ⟨y, x, hxy.symm, rfl, rfl⟩
    · obtain ⟨a, ha, huv | huv⟩ := hedge
      · exact Or.inr ⟨a, ha, Or.inr ⟨huv.1, huv.2⟩⟩
      · exact Or.inr ⟨a, ha, Or.inl ⟨huv.1, huv.2⟩⟩
  loopless := ⟨by
    intro u huu
    rcases huu with hstate | hedge
    · obtain ⟨x, y, hxy, hx, hy⟩ := hstate
      have hxy' : x = y := fkRectLayerInputEmbed_injective (hx.trans hy.symm)
      exact state.loopless.irrefl x (hxy' ▸ hxy)
    · obtain ⟨a, _, huu | huu⟩ := hedge
      · exact fkRectLayerEdgeEndpoints_ne hW evenRow a
          (huu.1.trans huu.2.symm)
      · exact fkRectLayerEdgeEndpoints_ne hW evenRow a
          (huu.2.trans huu.1.symm).symm⟩


def fkRectBoundaryLayerOutput {W : Nat} (hW : 0 < W)
    (evenRow : Bool) (state : FKRectBoundaryState W)
    (eta : Bool × Fin W -> Bool) : FKRectBoundaryState W where
  Adj u v := u ≠ v ∧
    (fkRectBoundaryLayerGraph hW evenRow state eta).Reachable
      (fkRectLayerOutputEmbed u) (fkRectLayerOutputEmbed v)
  symm := by
    rintro u v ⟨huv, hreach⟩
    exact ⟨huv.symm, hreach.symm⟩
  loopless := ⟨by simp⟩

theorem fkRectBoundaryLayerOutput_eq_finiteBoundaryConnectivityGraph
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) (eta : Bool × Fin W -> Bool) :
    fkRectBoundaryLayerOutput hW evenRow state eta =
      finiteBoundaryConnectivityGraph
        (fkRectBoundaryLayerGraph hW evenRow state eta)
        fkRectLayerOutputEmbed := rfl

theorem finiteBoundaryConnectivityGraph_isConnectivity
    {V B : Type*} (G : SimpleGraph V) (embed : B -> V) :
    ∀ u v,
      (finiteBoundaryConnectivityGraph G embed).Adj u v ↔
        u ≠ v ∧
          (finiteBoundaryConnectivityGraph G embed).Reachable u v := by
  intro u v
  rw [finiteBoundaryConnectivityGraph_reachable_iff]
  rfl

theorem fkRectBoundaryLayerOutput_isConnectivity
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) (eta : Bool × Fin W -> Bool) :
    (fkRectBoundaryLayerOutput hW evenRow state eta).IsConnectivity := by
  rw [fkRectBoundaryLayerOutput_eq_finiteBoundaryConnectivityGraph]
  exact finiteBoundaryConnectivityGraph_isConnectivity _ _



def fkRectBoundaryConnectivityLayerOutput
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryConnectivityState W)
    (eta : Bool × Fin W -> Bool) : FKRectBoundaryConnectivityState W :=
  ⟨fkRectBoundaryLayerOutput hW evenRow state.1 eta,
    fkRectBoundaryLayerOutput_isConnectivity hW evenRow state.1 eta⟩



def fkRectBoundaryLayerClosedCount {W : Nat} (hW : 0 < W)
    (evenRow : Bool) (state : FKRectBoundaryState W)
    (eta : Bool × Fin W -> Bool) : Nat := by
  classical
  let G := fkRectBoundaryLayerGraph hW evenRow state eta
  exact (Finset.univ.filter fun C : G.ConnectedComponent =>
    ∀ u : Bool × Fin W, G.connectedComponentMk
      (fkRectLayerOutputEmbed u) ≠ C).card



theorem fkRectBoundaryLayer_component_count
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) (eta : Bool × Fin W -> Bool) :
    Fintype.card
        (fkRectBoundaryLayerGraph hW evenRow state eta).ConnectedComponent =
      fkRectBoundaryLayerClosedCount hW evenRow state eta +
        Fintype.card
          (fkRectBoundaryLayerOutput hW evenRow state eta).ConnectedComponent := by
  simpa [fkRectBoundaryLayerClosedCount,
    fkRectBoundaryLayerOutput_eq_finiteBoundaryConnectivityGraph] using
      finite_component_count_eq_closed_add_boundary
        (fkRectBoundaryLayerGraph hW evenRow state eta)
        (fkRectLayerOutputEmbed : Bool × Fin W -> FKRectLayerVertex W)



def fkRectBoundaryVerticalLayer {W : Nat} : Bool × Fin W -> Bool :=
  fun a => a.1


def fkRectLayerCollapse {W : Nat} (u : FKRectLayerVertex W) :
    Bool × Fin W :=
  (if u.1 = fkRectLayerInitialRole then false else true, u.2)

@[simp] theorem fkRectLayerCollapse_inputEmbed {W : Nat}
    (u : Bool × Fin W) :
    fkRectLayerCollapse (fkRectLayerInputEmbed u) = u := by
  rcases u with ⟨b, x⟩
  cases b <;> simp [fkRectLayerCollapse, fkRectLayerInputEmbed,
    fkRectLayerInitialRole, fkRectLayerOldRole]

@[simp] theorem fkRectLayerCollapse_outputEmbed {W : Nat}
    (u : Bool × Fin W) :
    fkRectLayerCollapse (fkRectLayerOutputEmbed u) = u := by
  rcases u with ⟨b, x⟩
  cases b <;> simp [fkRectLayerCollapse, fkRectLayerOutputEmbed,
    fkRectLayerInitialRole, fkRectLayerNewRole]

theorem fkRectBoundaryVerticalLayer_adj_collapse_reachable
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) {u v : FKRectLayerVertex W}
    (huv : (fkRectBoundaryLayerGraph hW evenRow state
      fkRectBoundaryVerticalLayer).Adj u v) :
    state.Reachable (fkRectLayerCollapse u) (fkRectLayerCollapse v) := by
  rcases huv with hstate | hedge
  · obtain ⟨x, y, hxy, rfl, rfl⟩ := hstate
    simpa using hxy.reachable
  · obtain ⟨a, ha, huv | huv⟩ := hedge
    all_goals
      rcases a with ⟨dir, x⟩
      cases dir
      · simp [fkRectBoundaryVerticalLayer] at ha
      · rcases huv with ⟨rfl, rfl⟩
        simp [fkRectLayerEdgeEndpoints, fkRectLayerCollapse,
          fkRectLayerOldRole, fkRectLayerNewRole,
          fkRectLayerInitialRole]

theorem fkRectBoundaryVerticalLayer_reachable_collapse
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) {u v : FKRectLayerVertex W}
    (huv : (fkRectBoundaryLayerGraph hW evenRow state
      fkRectBoundaryVerticalLayer).Reachable u v) :
    state.Reachable (fkRectLayerCollapse u) (fkRectLayerCollapse v) := by
  rcases huv with ⟨p⟩
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj p ih =>
      exact (fkRectBoundaryVerticalLayer_adj_collapse_reachable
        hW evenRow state hadj).trans ih

theorem fkRectBoundaryVerticalLayer_input_reachable
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) {u v : Bool × Fin W}
    (huv : state.Reachable u v) :
    (fkRectBoundaryLayerGraph hW evenRow state
      fkRectBoundaryVerticalLayer).Reachable
        (fkRectLayerInputEmbed u) (fkRectLayerInputEmbed v) := by
  rcases huv with ⟨p⟩
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj p ih =>
      exact (show (fkRectBoundaryLayerGraph hW evenRow state
        fkRectBoundaryVerticalLayer).Adj
          (fkRectLayerInputEmbed _) (fkRectLayerInputEmbed _) from
            Or.inl ⟨_, _, hadj, rfl, rfl⟩).reachable.trans ih

theorem fkRectBoundaryVerticalLayer_input_output_reachable
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) (u : Bool × Fin W) :
    (fkRectBoundaryLayerGraph hW evenRow state
      fkRectBoundaryVerticalLayer).Reachable
        (fkRectLayerInputEmbed u) (fkRectLayerOutputEmbed u) := by
  rcases u with ⟨b, x⟩
  cases b
  · exact SimpleGraph.Reachable.refl _
  · apply SimpleGraph.Adj.reachable
    exact Or.inr ⟨(true, x), rfl, Or.inl ⟨by
      simp [fkRectLayerEdgeEndpoints, fkRectLayerInputEmbed,
        fkRectLayerOldRole], by
      simp [fkRectLayerEdgeEndpoints, fkRectLayerOutputEmbed,
        fkRectLayerNewRole]⟩⟩

theorem fkRectBoundaryVerticalLayer_output_reachable_iff
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) (u v : Bool × Fin W) :
    (fkRectBoundaryLayerGraph hW evenRow state
      fkRectBoundaryVerticalLayer).Reachable
        (fkRectLayerOutputEmbed u) (fkRectLayerOutputEmbed v) ↔
      state.Reachable u v := by
  constructor
  · intro h
    simpa using fkRectBoundaryVerticalLayer_reachable_collapse
      hW evenRow state h
  · intro h
    exact (fkRectBoundaryVerticalLayer_input_output_reachable
      hW evenRow state u).symm.trans
        ((fkRectBoundaryVerticalLayer_input_reachable
          hW evenRow state h).trans
          (fkRectBoundaryVerticalLayer_input_output_reachable
            hW evenRow state v))



theorem fkRectBoundaryLayerOutput_vertical
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) (hstate : state.IsConnectivity) :
    fkRectBoundaryLayerOutput hW evenRow state
      fkRectBoundaryVerticalLayer = state := by
  ext u v
  rw [hstate]
  exact and_congr_right fun _ =>
    fkRectBoundaryVerticalLayer_output_reachable_iff
      hW evenRow state u v


def fkRectBoundaryLayerOpenCount {W : Nat}
    (eta : Bool × Fin W -> Bool) : Nat :=
  (Finset.univ.filter fun a => eta a = true).card


def fkRectBoundaryOpenLayerIndices {W : Nat}
    (eta : Bool × Fin W -> Bool) : List (Bool × Fin W) :=
  (Finset.univ.filter fun a => eta a = true).toList


def fkRectBoundaryOpenLayerEdges {W : Nat} (hW : 0 < W)
    (evenRow : Bool) (eta : Bool × Fin W -> Bool) :
    List (FKRectLayerVertex W × FKRectLayerVertex W) :=
  (fkRectBoundaryOpenLayerIndices eta).map
    (fkRectLayerEdgeEndpoints hW evenRow)



theorem fkRectBoundaryLayerGraph_eq_edgeRun
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) (eta : Bool × Fin W -> Bool) :
    fkRectBoundaryLayerGraph hW evenRow state eta =
      finiteBoundaryEdgeRun id
        (fkRectBoundaryLayerGraph hW evenRow state (fun _ => false))
        (fkRectBoundaryOpenLayerEdges hW evenRow eta) := by
  classical
  ext u v
  rw [finiteBoundaryEdgeRun_adj_iff]
  unfold fkRectBoundaryLayerGraph fkRectBoundaryOpenLayerEdges
    fkRectBoundaryOpenLayerIndices
  simp only [Bool.false_eq_true, ↓reduceIte, exists_and_left,
    List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ,
    true_and, SimpleGraph.edge_adj, id_eq]
  constructor
  · rintro (hstate | ⟨a, ha, huv⟩)
    · exact Or.inl (Or.inl hstate)
    · have hne : u ≠ v := by
        intro huvEq
        apply fkRectLayerEdgeEndpoints_ne hW evenRow a
        rcases huv with huv | huv
        · exact huv.1.trans (huvEq.trans huv.2.symm)
        · exact (huv.2.trans (huvEq.trans huv.1.symm)).symm
      refine Or.inr ⟨fkRectLayerEdgeEndpoints hW evenRow a,
        ⟨a, ha, rfl⟩, ⟨?_, hne⟩⟩
      rcases huv with huv | huv
      · exact Or.inl ⟨huv.1.symm, huv.2.symm⟩
      · exact Or.inr ⟨huv.2.symm, huv.1.symm⟩
  · rintro (hbase | ⟨e, ⟨a, ha, rfl⟩, hedge⟩)
    · rcases hbase with hstate | ⟨hfalse, _⟩
      · exact Or.inl hstate
      · contradiction
    · refine Or.inr ⟨a, ha, ?_⟩
      rcases hedge.1 with hedge | hedge
      · exact Or.inl ⟨hedge.1.symm, hedge.2.symm⟩
      · exact Or.inr ⟨hedge.2.symm, hedge.1.symm⟩


def fkRectBoundaryEmptyLayer {W : Nat} : Bool × Fin W -> Bool :=
  fun _ => false

theorem fkRectBoundaryEmptyLayer_new_reachable_iff
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) (x : Fin W) (v : FKRectLayerVertex W) :
    (fkRectBoundaryLayerGraph hW evenRow state
      fkRectBoundaryEmptyLayer).Reachable
      (fkRectLayerNewRole, x) v ↔ v = (fkRectLayerNewRole, x) := by
  have hisolated :
      (fkRectBoundaryLayerGraph hW evenRow state
        fkRectBoundaryEmptyLayer).neighborSet (fkRectLayerNewRole, x) = ∅ := by
    ext w
    simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false, iff_false]
    intro hadj
    rcases hadj with hstate | hedge
    · obtain ⟨u, z, _, hu, _⟩ := hstate
      rcases u with ⟨b, y⟩
      cases b <;> simp [fkRectLayerInputEmbed, fkRectLayerInitialRole,
        fkRectLayerOldRole, fkRectLayerNewRole] at hu
    · obtain ⟨a, ha, _⟩ := hedge
      simp [fkRectBoundaryEmptyLayer] at ha
  constructor
  · intro hreach
    by_contra hne
    exact (SimpleGraph.not_reachable_of_neighborSet_left_eq_empty (Ne.symm hne) hisolated)
      hreach
  · rintro rfl
    exact SimpleGraph.Reachable.refl _

theorem fkRectBoundaryEmptyLayer_input_reachable_iff
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) (u v : Bool × Fin W) :
    (fkRectBoundaryLayerGraph hW evenRow state
      fkRectBoundaryEmptyLayer).Reachable
        (fkRectLayerInputEmbed u) (fkRectLayerInputEmbed v) ↔
      state.Reachable u v := by
  let collapseHom :
      fkRectBoundaryLayerGraph hW evenRow state fkRectBoundaryEmptyLayer →g
        state :=
    { toFun := fkRectLayerCollapse
      map_rel' := by
        intro a b hab
        rcases hab with hstate | hedge
        · obtain ⟨x, y, hxy, rfl, rfl⟩ := hstate
          simpa using hxy
        · obtain ⟨x, hx, _⟩ := hedge
          simp [fkRectBoundaryEmptyLayer] at hx }
  let inputHom : state →g
      fkRectBoundaryLayerGraph hW evenRow state fkRectBoundaryEmptyLayer :=
    { toFun := fkRectLayerInputEmbed
      map_rel' := by
        intro a b hab
        exact Or.inl ⟨a, b, hab, rfl, rfl⟩ }
  constructor
  · intro h
    simpa [collapseHom] using h.map collapseHom
  · intro h
    exact h.map inputHom



noncomputable def fkRectBoundaryEmptyLayerClosedComponentEquiv
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) :
    Fin W ≃
      {C : (fkRectBoundaryLayerGraph hW evenRow state
          fkRectBoundaryEmptyLayer).ConnectedComponent //
        ∀ u : Bool × Fin W,
          (fkRectBoundaryLayerGraph hW evenRow state
            fkRectBoundaryEmptyLayer).connectedComponentMk
              (fkRectLayerInputEmbed u) ≠ C} := by
  let G := fkRectBoundaryLayerGraph hW evenRow state fkRectBoundaryEmptyLayer
  let f : Fin W -> {C : G.ConnectedComponent //
      ∀ u : Bool × Fin W, G.connectedComponentMk
        (fkRectLayerInputEmbed u) ≠ C} := fun x =>
    ⟨G.connectedComponentMk (fkRectLayerNewRole, x), by
      intro u h
      have hreach : G.Reachable (fkRectLayerNewRole, x)
          (fkRectLayerInputEmbed u) :=
        SimpleGraph.ConnectedComponent.exact h.symm
      have heq := (fkRectBoundaryEmptyLayer_new_reachable_iff
        hW evenRow state x (fkRectLayerInputEmbed u)).1 hreach
      rcases u with ⟨b, y⟩
      cases b <;> simp [fkRectLayerInputEmbed, fkRectLayerInitialRole,
        fkRectLayerOldRole, fkRectLayerNewRole] at heq⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    have hreach : G.Reachable (fkRectLayerNewRole, x)
        (fkRectLayerNewRole, y) :=
      SimpleGraph.ConnectedComponent.exact (congrArg Subtype.val hxy)
    have heq := (fkRectBoundaryEmptyLayer_new_reachable_iff
      hW evenRow state x (fkRectLayerNewRole, y)).1 hreach
    exact (congrArg Prod.snd heq).symm
  · rintro ⟨C, hC⟩
    obtain ⟨v, hv⟩ := Quot.exists_rep C
    have hval : v.1.val = 0 ∨ v.1.val = 1 ∨ v.1.val = 2 := by omega
    rcases hval with hzero | hone | htwo
    · exfalso
      apply hC (false, v.2)
      calc
        G.connectedComponentMk (fkRectLayerInputEmbed (false, v.2)) =
            G.connectedComponentMk v := by
              apply congrArg G.connectedComponentMk
              apply Prod.ext
              · apply Fin.ext
                simpa [fkRectLayerInputEmbed, fkRectLayerInitialRole] using hzero.symm
              · rfl
        _ = C := hv
    · exfalso
      apply hC (true, v.2)
      calc
        G.connectedComponentMk (fkRectLayerInputEmbed (true, v.2)) =
            G.connectedComponentMk v := by
              apply congrArg G.connectedComponentMk
              apply Prod.ext
              · apply Fin.ext
                simpa [fkRectLayerInputEmbed, fkRectLayerOldRole] using hone.symm
              · rfl
        _ = C := hv
    · refine ⟨v.2, ?_⟩
      apply Subtype.ext
      calc
        G.connectedComponentMk (fkRectLayerNewRole, v.2) =
            G.connectedComponentMk v := by
              apply congrArg G.connectedComponentMk
              apply Prod.ext
              · apply Fin.ext
                simpa [fkRectLayerNewRole] using htwo.symm
              · rfl
        _ = C := hv

theorem fkRectBoundaryEmptyLayer_boundaryGraph_eq
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) (hstate : state.IsConnectivity) :
    finiteBoundaryConnectivityGraph
        (fkRectBoundaryLayerGraph hW evenRow state fkRectBoundaryEmptyLayer)
        fkRectLayerInputEmbed = state := by
  ext u v
  change (u ≠ v ∧
      (fkRectBoundaryLayerGraph hW evenRow state
        fkRectBoundaryEmptyLayer).Reachable
          (fkRectLayerInputEmbed u) (fkRectLayerInputEmbed v)) ↔ state.Adj u v
  rw [fkRectBoundaryEmptyLayer_input_reachable_iff, hstate]



theorem fkRectBoundaryEmptyLayer_component_count
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) (hstate : state.IsConnectivity) :
    Fintype.card (fkRectBoundaryLayerGraph hW evenRow state
        fkRectBoundaryEmptyLayer).ConnectedComponent =
      Fintype.card state.ConnectedComponent + W := by
  classical
  let G := fkRectBoundaryLayerGraph hW evenRow state fkRectBoundaryEmptyLayer
  have hsplit := finite_component_count_eq_closed_add_boundary
    G (fkRectLayerInputEmbed : Bool × Fin W -> FKRectLayerVertex W)
  have hclosed :
      (Finset.univ.filter fun C : G.ConnectedComponent =>
        ∀ u : Bool × Fin W, G.connectedComponentMk
          (fkRectLayerInputEmbed u) ≠ C).card = W := by
    rw [← Fintype.card_subtype]
    simpa [G] using Fintype.card_congr
      (fkRectBoundaryEmptyLayerClosedComponentEquiv hW evenRow state).symm
  rw [hclosed, fkRectBoundaryEmptyLayer_boundaryGraph_eq hW evenRow state hstate]
    at hsplit
  simpa [G, Nat.add_comm] using hsplit





def fkRectBoundaryInitialState (W : Nat) : FKRectBoundaryState W where
  Adj u v := u.2 = v.2 ∧ u.1 ≠ v.1
  symm := by
    rintro u v ⟨hcoord, hbool⟩
    exact ⟨hcoord.symm, hbool.symm⟩
  loopless := ⟨by simp⟩



def FKRectStripVertex (W : Nat) : Nat -> Type
  | 0 => Fin W
  | n + 1 => FKRectStripVertex W n ⊕ Fin W

noncomputable def fkRectStripVertexFintype (W : Nat) :
    (n : Nat) -> Fintype (FKRectStripVertex W n)
  | 0 => inferInstanceAs (Fintype (Fin W))
  | n + 1 => @instFintypeSum (FKRectStripVertex W n) (Fin W)
      (fkRectStripVertexFintype W n) inferInstance

noncomputable instance (W n : Nat) : Fintype (FKRectStripVertex W n) :=
  fkRectStripVertexFintype W n

noncomputable instance (W n : Nat) : DecidableEq (FKRectStripVertex W n) :=
  Classical.decEq _


def fkRectStripInitial {W : Nat} : (n : Nat) -> Fin W -> FKRectStripVertex W n
  | 0 => id
  | n + 1 => Sum.inl ∘ fkRectStripInitial n


def fkRectStripCurrent {W : Nat} : (n : Nat) -> Fin W -> FKRectStripVertex W n
  | 0 => id
  | _ + 1 => Sum.inr



def fkRectStripBoundary {W : Nat} (n : Nat) :
    Bool × Fin W -> FKRectStripVertex W n := fun u =>
  if u.1 then fkRectStripCurrent n u.2 else fkRectStripInitial n u.2

@[simp] theorem fkRectStripBoundary_false {W : Nat} (n : Nat) (x : Fin W) :
    fkRectStripBoundary n (false, x) = fkRectStripInitial n x := rfl

@[simp] theorem fkRectStripBoundary_true {W : Nat} (n : Nat) (x : Fin W) :
    fkRectStripBoundary n (true, x) = fkRectStripCurrent n x := rfl


def fkRectStripLayerEmbed {W : Nat} (n : Nat) :
    FKRectLayerVertex W -> FKRectStripVertex W (n + 1) := fun u =>
  if u.1 = fkRectLayerInitialRole then
    Sum.inl (fkRectStripInitial n u.2)
  else if u.1 = fkRectLayerOldRole then
    Sum.inl (fkRectStripCurrent n u.2)
  else
    Sum.inr u.2

@[simp] theorem fkRectStripLayerEmbed_initial {W : Nat} (n : Nat) (x : Fin W) :
    fkRectStripLayerEmbed n (fkRectLayerInitialRole, x) =
      Sum.inl (fkRectStripInitial n x) := by
  simp [fkRectStripLayerEmbed, fkRectLayerInitialRole,
    fkRectLayerOldRole]

@[simp] theorem fkRectStripLayerEmbed_old {W : Nat} (n : Nat) (x : Fin W) :
    fkRectStripLayerEmbed n (fkRectLayerOldRole, x) =
      Sum.inl (fkRectStripCurrent n x) := by
  simp [fkRectStripLayerEmbed, fkRectLayerInitialRole,
    fkRectLayerOldRole]

@[simp] theorem fkRectStripLayerEmbed_new {W : Nat} (n : Nat) (x : Fin W) :
    fkRectStripLayerEmbed n (fkRectLayerNewRole, x) = Sum.inr x := by
  simp [fkRectStripLayerEmbed, fkRectLayerInitialRole,
    fkRectLayerOldRole, fkRectLayerNewRole]

@[simp] theorem fkRectStripLayerEmbed_input {W : Nat} (n : Nat)
    (u : Bool × Fin W) :
    fkRectStripLayerEmbed n (fkRectLayerInputEmbed u) =
      Sum.inl (fkRectStripBoundary n u) := by
  cases u with
  | mk b x =>
      cases b <;> simp [fkRectLayerInputEmbed]

@[simp] theorem fkRectStripLayerEmbed_output {W : Nat} (n : Nat)
    (u : Bool × Fin W) :
    fkRectStripLayerEmbed n (fkRectLayerOutputEmbed u) =
      fkRectStripBoundary (n + 1) u := by
  cases u with
  | mk b x =>
      cases b <;> simp [fkRectLayerOutputEmbed, fkRectStripBoundary,
        fkRectStripInitial, fkRectStripCurrent]


def fkRectStripGraph {W : Nat} (hW : 0 < W) :
    (n : Nat) -> (Fin n -> Bool × (Bool × Fin W -> Bool)) ->
      SimpleGraph (FKRectStripVertex W n)
  | 0, _ => ⊥
  | n + 1, layers =>
      finiteBoundaryEdgeRun (fkRectStripLayerEmbed n)
        ((fkRectStripGraph hW n (fun i => layers i.castSucc)).sum ⊥)
        (fkRectBoundaryOpenLayerEdges hW (layers (Fin.last n)).1
          (layers (Fin.last n)).2)


def fkRectStripState {W : Nat} (hW : 0 < W) :
    (n : Nat) -> (Fin n -> Bool × (Bool × Fin W -> Bool)) ->
      FKRectBoundaryState W
  | 0, _ => fkRectBoundaryInitialState W
  | n + 1, layers =>
      fkRectBoundaryLayerOutput hW (layers (Fin.last n)).1
        (fkRectStripState hW n (fun i => layers i.castSucc))
        (layers (Fin.last n)).2


def fkRectStripClosedCount {W : Nat} (hW : 0 < W) :
    (n : Nat) -> (Fin n -> Bool × (Bool × Fin W -> Bool)) -> Nat
  | 0, _ => 0
  | n + 1, layers =>
      fkRectStripClosedCount hW n (fun i => layers i.castSucc) +
        fkRectBoundaryLayerClosedCount hW (layers (Fin.last n)).1
          (fkRectStripState hW n (fun i => layers i.castSucc))
          (layers (Fin.last n)).2

theorem fkRectStripGraph_succ_adj_iff
    {W : Nat} (hW : 0 < W) (n : Nat)
    (layers : Fin (n + 1) -> Bool × (Bool × Fin W -> Bool))
    (u v : FKRectStripVertex W (n + 1)) :
    (fkRectStripGraph hW (n + 1) layers).Adj u v ↔
      ((fkRectStripGraph hW n (fun i => layers i.castSucc)).sum
        (⊥ : SimpleGraph (Fin W))).Adj u v ∨
      ∃ a : Bool × Fin W, (layers (Fin.last n)).2 a = true ∧
        (SimpleGraph.edge
          (fkRectStripLayerEmbed n
            (fkRectLayerEdgeEndpoints hW (layers (Fin.last n)).1 a).1)
          (fkRectStripLayerEmbed n
            (fkRectLayerEdgeEndpoints hW (layers (Fin.last n)).1 a).2)).Adj u v := by
  rw [fkRectStripGraph, finiteBoundaryEdgeRun_adj_iff]
  unfold fkRectBoundaryOpenLayerEdges fkRectBoundaryOpenLayerIndices
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter,
    Finset.mem_univ, true_and]
  aesop


theorem fkRectOpenEdgeCount_eq_sum_layerOpenCount
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectOpenEdgeCount R omega =
      ∑ y : Fin R.height,
        fkRectBoundaryLayerOpenCount (fkRectConfigurationLayer R omega y) := by
  classical
  unfold fkRectOpenEdgeCount fkRectBoundaryLayerOpenCount
  simp only [Finset.card_filter, Fintype.sum_prod_type,
    fkRectConfigurationLayer]
  calc
    (∑ b : Bool, ∑ x : Fin R.width, ∑ y : Fin R.height,
        if omega (b, (x, y)) = true then 1 else 0) =
        ∑ b : Bool, ∑ y : Fin R.height, ∑ x : Fin R.width,
          if omega (b, (x, y)) = true then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro b hb
            rw [Finset.sum_comm]
    _ = ∑ y : Fin R.height, ∑ b : Bool, ∑ x : Fin R.width,
          if omega (b, (x, y)) = true then 1 else 0 := by
            rw [Finset.sum_comm]


def fkRectBoundaryLayerWeight {W : Nat} (hW : 0 < W)
    (q : Real) (evenRow : Bool) (state : FKRectBoundaryState W)
    (eta : Bool × Fin W -> Bool) : Real :=
  Real.sqrt q ^ fkRectBoundaryLayerOpenCount eta *
    q ^ fkRectBoundaryLayerClosedCount hW evenRow state eta


def fkRectBoundaryRunState {W : Nat} (hW : 0 < W) :
    FKRectBoundaryState W ->
      List (Bool × (Bool × Fin W -> Bool)) -> FKRectBoundaryState W
  | state, [] => state
  | state, layer :: layers =>
      fkRectBoundaryRunState hW
        (fkRectBoundaryLayerOutput hW layer.1 state layer.2) layers


def fkRectBoundaryRunClosedCount {W : Nat} (hW : 0 < W) :
    FKRectBoundaryState W ->
      List (Bool × (Bool × Fin W -> Bool)) -> Nat
  | _, [] => 0
  | state, layer :: layers =>
      fkRectBoundaryLayerClosedCount hW layer.1 state layer.2 +
        fkRectBoundaryRunClosedCount hW
          (fkRectBoundaryLayerOutput hW layer.1 state layer.2) layers


def fkRectBoundaryRunOpenCount {W : Nat} :
    List (Bool × (Bool × Fin W -> Bool)) -> Nat
  | [] => 0
  | layer :: layers =>
      fkRectBoundaryLayerOpenCount layer.2 +
        fkRectBoundaryRunOpenCount layers


def fkRectBoundaryRunWeight {W : Nat} (hW : 0 < W) (q : Real) :
    FKRectBoundaryState W ->
      List (Bool × (Bool × Fin W -> Bool)) -> Real
  | _, [] => 1
  | state, layer :: layers =>
      fkRectBoundaryLayerWeight hW q layer.1 state layer.2 *
        fkRectBoundaryRunWeight hW q
          (fkRectBoundaryLayerOutput hW layer.1 state layer.2) layers

theorem fkRectBoundaryRunWeight_eq
    {W : Nat} (hW : 0 < W) (q : Real)
    (state : FKRectBoundaryState W)
    (layers : List (Bool × (Bool × Fin W -> Bool))) :
    fkRectBoundaryRunWeight hW q state layers =
      Real.sqrt q ^ fkRectBoundaryRunOpenCount layers *
        q ^ fkRectBoundaryRunClosedCount hW state layers := by
  induction layers generalizing state with
  | nil => simp [fkRectBoundaryRunWeight, fkRectBoundaryRunOpenCount,
      fkRectBoundaryRunClosedCount]
  | cons layer layers ih =>
      rw [fkRectBoundaryRunWeight, fkRectBoundaryRunOpenCount,
        fkRectBoundaryRunClosedCount, fkRectBoundaryLayerWeight, ih]
      rw [pow_add, pow_add]
      ring

theorem fkRectBoundaryRunOpenCount_eq_sum
    {W : Nat} (layers : List (Bool × (Bool × Fin W -> Bool))) :
    fkRectBoundaryRunOpenCount layers =
      (layers.map fun layer =>
        fkRectBoundaryLayerOpenCount layer.2).sum := by
  induction layers with
  | nil => rfl
  | cons layer layers ih =>
      simp only [fkRectBoundaryRunOpenCount, List.map_cons, List.sum_cons, ih]


def fkRectBoundarySeamRow (R : FKRectTorus) : Fin R.height :=
  ⟨0, R.height_pos⟩


def fkRectBoundaryNonSeamRow (R : FKRectTorus)
    (i : Fin (R.height - 1)) : Fin R.height :=
  finCongr (Nat.sub_add_cancel
    (Nat.one_le_iff_ne_zero.mpr R.height_pos.ne')) i.succ

@[simp] theorem fkRectBoundaryNonSeamRow_val (R : FKRectTorus)
    (i : Fin (R.height - 1)) :
    (fkRectBoundaryNonSeamRow R i).val = i.val + 1 := rfl


theorem fkRect_sum_rows_eq_seam_add_nonSeam
    (R : FKRectTorus) (f : Fin R.height -> Nat) :
    (∑ y, f y) = f (fkRectBoundarySeamRow R) +
      ∑ i : Fin (R.height - 1), f (fkRectBoundaryNonSeamRow R i) := by
  let e : Fin (R.height - 1 + 1) ≃ Fin R.height :=
    finCongr (Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr R.height_pos.ne'))
  rw [← Equiv.sum_comp e f, Fin.sum_univ_succ]
  rfl


def fkRectConfigurationNonSeamLayers (R : FKRectTorus)
    (omega : R.Configuration) :
    List (Bool × (Bool × Fin R.width -> Bool)) :=
  List.ofFn fun i : Fin (R.height - 1) =>
    let y := fkRectBoundaryNonSeamRow R i
    (decide (Even y.val), fkRectConfigurationLayer R omega y)



theorem fkRectOpenEdgeCount_eq_run_add_seam
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectOpenEdgeCount R omega =
      fkRectBoundaryRunOpenCount
          (fkRectConfigurationNonSeamLayers R omega) +
        fkRectBoundaryLayerOpenCount
          (fkRectConfigurationLayer R omega (fkRectBoundarySeamRow R)) := by
  rw [fkRectOpenEdgeCount_eq_sum_layerOpenCount,
    fkRect_sum_rows_eq_seam_add_nonSeam]
  rw [Nat.add_comm]
  congr 1
  rw [fkRectBoundaryRunOpenCount_eq_sum]
  simp [fkRectConfigurationNonSeamLayers, List.map_ofFn,
    List.sum_ofFn]


def fkRectBoundaryLayerTransfer {W : Nat} (hW : 0 < W)
    (q : Real) (evenRow : Bool) :
    Matrix (FKRectBoundaryState W) (FKRectBoundaryState W) Real := by
  classical
  exact fun source target =>
    ∑ eta : Bool × Fin W -> Bool,
      if fkRectBoundaryLayerOutput hW evenRow source eta = target then
        fkRectBoundaryLayerWeight hW q evenRow source eta
      else 0


def fkRectBoundaryTwoLayerTransfer {W : Nat} (hW : 0 < W)
    (q : Real) :
    Matrix (FKRectBoundaryState W) (FKRectBoundaryState W) Real :=
  fkRectBoundaryLayerTransfer hW q false *
    fkRectBoundaryLayerTransfer hW q true

theorem fkRectBoundaryInitialState_reachable_iff (W : Nat)
    (u v : Bool × Fin W) :
    (fkRectBoundaryInitialState W).Reachable u v ↔ u.2 = v.2 := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => rfl
    | cons hadj p ih => exact hadj.1.trans ih
  · intro hcoord
    by_cases huv : u = v
    · subst v
      exact SimpleGraph.Reachable.refl _
    · apply SimpleGraph.Adj.reachable
      exact ⟨hcoord, fun hbool => huv (Prod.ext hbool hcoord)⟩

theorem fkRectBoundaryInitialState_isConnectivity (W : Nat) :
    (fkRectBoundaryInitialState W).IsConnectivity := by
  intro u v
  rw [fkRectBoundaryInitialState_reachable_iff]
  constructor
  · intro h
    exact ⟨fun huv => (fkRectBoundaryInitialState W).loopless.irrefl u
      (huv ▸ h), h.1⟩
  · rintro ⟨huv, hcoord⟩
    exact ⟨hcoord, fun hbool => huv (Prod.ext hbool hcoord)⟩


def fkRectBoundaryInitialConnectivityState (W : Nat) :
    FKRectBoundaryConnectivityState W :=
  ⟨fkRectBoundaryInitialState W,
    fkRectBoundaryInitialState_isConnectivity W⟩



private theorem walk_sum_inl_aux
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {a z : V ⊕ W} (p : (G.sum H).Walk a z) :
    ∀ u : V, a = Sum.inl u →
      ∃ v : V, z = Sum.inl v ∧ Nonempty (G.Walk u v) := by
  induction p with
  | nil =>
      intro u hu
      exact ⟨u, hu, ⟨.nil⟩⟩
  | @cons a b z hab p ih =>
      intro u hu
      subst a
      cases b with
      | inl b =>
          simp only [SimpleGraph.sum_adj] at hab
          obtain ⟨v, hv, ⟨q⟩⟩ := ih b rfl
          exact ⟨v, hv, ⟨.cons hab q⟩⟩
      | inr b => simp only [SimpleGraph.sum_adj] at hab

private theorem walk_sum_inr_aux
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {a z : V ⊕ W} (p : (G.sum H).Walk a z) :
    ∀ u : W, a = Sum.inr u →
      ∃ v : W, z = Sum.inr v ∧ Nonempty (H.Walk u v) := by
  induction p with
  | nil =>
      intro u hu
      exact ⟨u, hu, ⟨.nil⟩⟩
  | @cons a b z hab p ih =>
      intro u hu
      subst a
      cases b with
      | inl b => simp only [SimpleGraph.sum_adj] at hab
      | inr b =>
          simp only [SimpleGraph.sum_adj] at hab
          obtain ⟨v, hv, ⟨q⟩⟩ := ih b rfl
          exact ⟨v, hv, ⟨.cons hab q⟩⟩

theorem simpleGraph_sum_reachable_inl_iff
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {u v : V} :
    (G.sum H).Reachable (Sum.inl u) (Sum.inl v) ↔ G.Reachable u v := by
  constructor
  · rintro ⟨p⟩
    obtain ⟨w, hw, h⟩ := walk_sum_inl_aux p u rfl
    simp only [Sum.inl.injEq] at hw
    subst w
    exact h
  · intro h
    exact h.map SimpleGraph.Embedding.sumInl.toHom

theorem simpleGraph_sum_reachable_inr_iff
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {u v : W} :
    (G.sum H).Reachable (Sum.inr u) (Sum.inr v) ↔ H.Reachable u v := by
  constructor
  · rintro ⟨p⟩
    obtain ⟨w, hw, h⟩ := walk_sum_inr_aux p u rfl
    simp only [Sum.inr.injEq] at hw
    subst w
    exact h
  · intro h
    exact h.map SimpleGraph.Embedding.sumInr.toHom

theorem simpleGraph_sum_not_reachable_inl_inr
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {u : V} {v : W} :
    ¬(G.sum H).Reachable (Sum.inl u) (Sum.inr v) := by
  rintro ⟨p⟩
  obtain ⟨w, hw, _⟩ := walk_sum_inl_aux p u rfl
  cases hw

theorem simpleGraph_sum_not_reachable_inr_inl
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {u : W} {v : V} :
    ¬(G.sum H).Reachable (Sum.inr u) (Sum.inl v) := by
  rintro ⟨p⟩
  obtain ⟨w, hw, _⟩ := walk_sum_inr_aux p u rfl
  cases hw



noncomputable def simpleGraph_sum_componentEquiv
    {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) :
    (G.sum H).ConnectedComponent ≃
      G.ConnectedComponent ⊕ H.ConnectedComponent := by
  let toSide : (G.sum H).ConnectedComponent ->
      G.ConnectedComponent ⊕ H.ConnectedComponent :=
    Quot.lift
      (fun z => match z with
        | Sum.inl v => Sum.inl (G.connectedComponentMk v)
        | Sum.inr w => Sum.inr (H.connectedComponentMk w))
      (by
        intro a b hab
        cases a with
        | inl a =>
            cases b with
            | inl b =>
                exact congrArg Sum.inl
                  (SimpleGraph.ConnectedComponent.sound
                    ((simpleGraph_sum_reachable_inl_iff).1 hab))
            | inr b => exact (simpleGraph_sum_not_reachable_inl_inr hab).elim
        | inr a =>
            cases b with
            | inl b => exact (simpleGraph_sum_not_reachable_inr_inl hab).elim
            | inr b =>
                exact congrArg Sum.inr
                  (SimpleGraph.ConnectedComponent.sound
                    ((simpleGraph_sum_reachable_inr_iff).1 hab)))
  let fromSide : G.ConnectedComponent ⊕ H.ConnectedComponent ->
      (G.sum H).ConnectedComponent
    | Sum.inl C => C.map SimpleGraph.Embedding.sumInl.toHom
    | Sum.inr C => C.map SimpleGraph.Embedding.sumInr.toHom
  refine
    { toFun := toSide
      invFun := fromSide
      left_inv := ?_
      right_inv := ?_ }
  · intro C
    refine SimpleGraph.ConnectedComponent.ind (G := G.sum H) ?_ C
    rintro (v | w) <;> rfl
  · rintro (C | C)
    · refine SimpleGraph.ConnectedComponent.ind (G := G) ?_ C
      intro v
      rfl
    · refine SimpleGraph.ConnectedComponent.ind (G := H) ?_ C
      intro w
      rfl

theorem simpleGraph_card_components_sum
    {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    Nat.card (G.sum H).ConnectedComponent =
      Nat.card G.ConnectedComponent + Nat.card H.ConnectedComponent := by
  rw [Nat.card_congr (simpleGraph_sum_componentEquiv G H), Nat.card_sum]



noncomputable def fkRectBoundaryInitialComponentEquiv (W : Nat) :
    (fkRectBoundaryInitialState W).ConnectedComponent ≃ Fin W := by
  let f : Fin W -> (fkRectBoundaryInitialState W).ConnectedComponent :=
    fun x => (fkRectBoundaryInitialState W).connectedComponentMk (false, x)
  exact (Equiv.ofBijective f ⟨by
    intro x y hxy
    exact (fkRectBoundaryInitialState_reachable_iff W (false, x) (false, y)).1
      (SimpleGraph.ConnectedComponent.exact hxy), by
    intro C
    refine SimpleGraph.ConnectedComponent.ind (G := fkRectBoundaryInitialState W)
      ?_ C
    rintro ⟨b, x⟩
    refine ⟨x, ?_⟩
    apply SimpleGraph.ConnectedComponent.sound
    exact (fkRectBoundaryInitialState_reachable_iff W (false, x) (b, x)).2 rfl⟩).symm

theorem fkRectBoundaryInitialState_component_count (W : Nat) :
    Nat.card (fkRectBoundaryInitialState W).ConnectedComponent = W := by
  rw [Nat.card_congr (fkRectBoundaryInitialComponentEquiv W), Nat.card_fin]

theorem fkRectStripState_isConnectivity
    {W : Nat} (hW : 0 < W) (n : Nat)
    (layers : Fin n -> Bool × (Bool × Fin W -> Bool)) :
    (fkRectStripState hW n layers).IsConnectivity := by
  cases n with
  | zero =>
      simpa [fkRectStripState] using fkRectBoundaryInitialState_isConnectivity W
  | succ n =>
      simp only [fkRectStripState]
      exact fkRectBoundaryLayerOutput_isConnectivity _ _ _ _

theorem fkRectBoundaryEmptyLayer_reachable_new_iff
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) (v : FKRectLayerVertex W) (x : Fin W) :
    (fkRectBoundaryLayerGraph hW evenRow state
      fkRectBoundaryEmptyLayer).Reachable v (fkRectLayerNewRole, x) ↔
      v = (fkRectLayerNewRole, x) := by
  rw [SimpleGraph.reachable_comm,
    fkRectBoundaryEmptyLayer_new_reachable_iff]




theorem fkRectStripExpanded_reachable_iff
    {W : Nat} (hW : 0 < W) (n : Nat)
    (layers : Fin n -> Bool × (Bool × Fin W -> Bool))
    (evenRow : Bool)
    (hprev : ∀ u v : Bool × Fin W,
      ((fkRectStripGraph hW n layers).Reachable
        (fkRectStripBoundary n u) (fkRectStripBoundary n v) ↔
          (fkRectStripState hW n layers).Reachable u v))
    (u v : FKRectLayerVertex W) :
    ((fkRectStripGraph hW n layers).sum (⊥ : SimpleGraph (Fin W))).Reachable
        (fkRectStripLayerEmbed n u) (fkRectStripLayerEmbed n v) ↔
      (fkRectBoundaryLayerGraph hW evenRow
        (fkRectStripState hW n layers) fkRectBoundaryEmptyLayer).Reachable
          u v := by
  rcases u with ⟨i, x⟩
  rcases v with ⟨j, y⟩
  fin_cases i <;> fin_cases j
  · simpa [fkRectStripLayerEmbed, fkRectLayerInputEmbed,
      fkRectLayerInitialRole, fkRectLayerOldRole, fkRectStripBoundary,
      simpleGraph_sum_reachable_inl_iff] using
        (hprev (false, x) (false, y)).trans
          (fkRectBoundaryEmptyLayer_input_reachable_iff hW evenRow
            (fkRectStripState hW n layers) (false, x) (false, y)).symm
  · simpa [fkRectStripLayerEmbed, fkRectLayerInputEmbed,
      fkRectLayerInitialRole, fkRectLayerOldRole, fkRectStripBoundary,
      simpleGraph_sum_reachable_inl_iff] using
        (hprev (false, x) (true, y)).trans
          (fkRectBoundaryEmptyLayer_input_reachable_iff hW evenRow
            (fkRectStripState hW n layers) (false, x) (true, y)).symm
  · simp [fkRectStripLayerEmbed, fkRectLayerInitialRole,
      fkRectLayerOldRole, fkRectLayerNewRole,
      simpleGraph_sum_not_reachable_inl_inr]
    simpa [fkRectLayerInitialRole, fkRectLayerNewRole] using
      (fkRectBoundaryEmptyLayer_reachable_new_iff hW evenRow
        (fkRectStripState hW n layers)
        (fkRectLayerInitialRole, x) y).not
  · simpa [fkRectStripLayerEmbed, fkRectLayerInputEmbed,
      fkRectLayerInitialRole, fkRectLayerOldRole, fkRectStripBoundary,
      simpleGraph_sum_reachable_inl_iff] using
        (hprev (true, x) (false, y)).trans
          (fkRectBoundaryEmptyLayer_input_reachable_iff hW evenRow
            (fkRectStripState hW n layers) (true, x) (false, y)).symm
  · simpa [fkRectStripLayerEmbed, fkRectLayerInputEmbed,
      fkRectLayerInitialRole, fkRectLayerOldRole, fkRectStripBoundary,
      simpleGraph_sum_reachable_inl_iff] using
        (hprev (true, x) (true, y)).trans
          (fkRectBoundaryEmptyLayer_input_reachable_iff hW evenRow
            (fkRectStripState hW n layers) (true, x) (true, y)).symm
  · simp [fkRectStripLayerEmbed, fkRectLayerInitialRole,
      fkRectLayerOldRole, fkRectLayerNewRole,
      simpleGraph_sum_not_reachable_inl_inr]
    simpa [fkRectLayerOldRole, fkRectLayerNewRole] using
      (fkRectBoundaryEmptyLayer_reachable_new_iff hW evenRow
        (fkRectStripState hW n layers)
        (fkRectLayerOldRole, x) y).not
  · simp [fkRectStripLayerEmbed, fkRectLayerInitialRole,
      fkRectLayerOldRole, fkRectLayerNewRole,
      simpleGraph_sum_not_reachable_inr_inl]
    simpa [fkRectLayerInitialRole, fkRectLayerNewRole] using
      (fkRectBoundaryEmptyLayer_new_reachable_iff hW evenRow
        (fkRectStripState hW n layers) x
        (fkRectLayerInitialRole, y)).not
  · simp [fkRectStripLayerEmbed, fkRectLayerInitialRole,
      fkRectLayerOldRole, fkRectLayerNewRole,
      simpleGraph_sum_not_reachable_inr_inl]
    simpa [fkRectLayerOldRole, fkRectLayerNewRole] using
      (fkRectBoundaryEmptyLayer_new_reachable_iff hW evenRow
        (fkRectStripState hW n layers) x
        (fkRectLayerOldRole, y)).not
  · change (((fkRectStripGraph hW n layers).sum
        (⊥ : SimpleGraph (Fin W))).Reachable (Sum.inr x) (Sum.inr y) ↔
      (fkRectBoundaryLayerGraph hW evenRow
        (fkRectStripState hW n layers) fkRectBoundaryEmptyLayer).Reachable
          (fkRectLayerNewRole, x) (fkRectLayerNewRole, y))
    rw [simpleGraph_sum_reachable_inr_iff, SimpleGraph.reachable_bot]
    simpa [fkRectLayerNewRole, eq_comm] using
      (fkRectBoundaryEmptyLayer_new_reachable_iff hW evenRow
        (fkRectStripState hW n layers) x
        (fkRectLayerNewRole, y)).symm



theorem fkRectStrip_boundary_reachable_iff
    {W : Nat} (hW : 0 < W) (n : Nat)
    (layers : Fin n -> Bool × (Bool × Fin W -> Bool))
    (u v : Bool × Fin W) :
    (fkRectStripGraph hW n layers).Reachable
        (fkRectStripBoundary n u) (fkRectStripBoundary n v) ↔
      (fkRectStripState hW n layers).Reachable u v := by
  induction n generalizing u v with
  | zero =>
      simpa [fkRectStripGraph, fkRectStripBoundary, fkRectStripInitial,
        fkRectStripCurrent, fkRectStripState, SimpleGraph.reachable_bot]
        using (fkRectBoundaryInitialState_reachable_iff W u v).symm
  | succ n ih =>
      let priorLayers : Fin n -> Bool × (Bool × Fin W -> Bool) :=
        fun i => layers i.castSucc
      let layer := layers (Fin.last n)
      have hbase : ∀ x y : FKRectLayerVertex W,
          ((fkRectStripGraph hW n priorLayers).sum
            (⊥ : SimpleGraph (Fin W))).Reachable
              (fkRectStripLayerEmbed n x) (fkRectStripLayerEmbed n y) ↔
            (fkRectBoundaryLayerGraph hW layer.1
              (fkRectStripState hW n priorLayers)
              fkRectBoundaryEmptyLayer).Reachable x y :=
        fkRectStripExpanded_reachable_iff hW n priorLayers layer.1
          (fun x y => ih priorLayers x y)
      change (finiteBoundaryEdgeRun (fkRectStripLayerEmbed n)
          ((fkRectStripGraph hW n priorLayers).sum (⊥ : SimpleGraph (Fin W)))
          (fkRectBoundaryOpenLayerEdges hW layer.1 layer.2)).Reachable
            (fkRectStripBoundary (n + 1) u)
            (fkRectStripBoundary (n + 1) v) ↔
        (fkRectBoundaryLayerOutput hW layer.1
          (fkRectStripState hW n priorLayers) layer.2).Reachable u v
      rw [← fkRectStripLayerEmbed_output n u,
        ← fkRectStripLayerEmbed_output n v]
      rw [finiteBoundaryEdgeRun_reachable_iff
        (fkRectStripLayerEmbed n)
        ((fkRectStripGraph hW n priorLayers).sum (⊥ : SimpleGraph (Fin W)))
        (fkRectBoundaryLayerGraph hW layer.1
          (fkRectStripState hW n priorLayers) fkRectBoundaryEmptyLayer)
        hbase]
      change (finiteBoundaryEdgeRun id
          (fkRectBoundaryLayerGraph hW layer.1
            (fkRectStripState hW n priorLayers) (fun _ => false))
          (fkRectBoundaryOpenLayerEdges hW layer.1 layer.2)).Reachable
            (fkRectLayerOutputEmbed u) (fkRectLayerOutputEmbed v) ↔
        (fkRectBoundaryLayerOutput hW layer.1
          (fkRectStripState hW n priorLayers) layer.2).Reachable u v
      rw [← fkRectBoundaryLayerGraph_eq_edgeRun hW layer.1
        (fkRectStripState hW n priorLayers) layer.2]
      rw [fkRectBoundaryLayerOutput_eq_finiteBoundaryConnectivityGraph,
        finiteBoundaryConnectivityGraph_reachable_iff]




theorem fkRectStrip_component_count
    {W : Nat} (hW : 0 < W) (n : Nat)
    (layers : Fin n -> Bool × (Bool × Fin W -> Bool)) :
    Nat.card (fkRectStripGraph hW n layers).ConnectedComponent =
      fkRectStripClosedCount hW n layers +
        Nat.card (fkRectStripState hW n layers).ConnectedComponent := by
  induction n with
  | zero =>
      rw [fkRectStripGraph, StatMech.Lattice.card_components_bot]
      have hvertices : Nat.card (FKRectStripVertex W 0) = W := by
        change Nat.card (Fin W) = W
        exact Nat.card_fin W
      rw [hvertices, fkRectStripClosedCount, fkRectStripState,
        fkRectBoundaryInitialState_component_count]
      simp
  | succ n ih =>
      let priorLayers : Fin n -> Bool × (Bool × Fin W -> Bool) :=
        fun i => layers i.castSucc
      let layer := layers (Fin.last n)
      let priorGraph := fkRectStripGraph hW n priorLayers
      let priorState := fkRectStripState hW n priorLayers
      let expandedGraph := priorGraph.sum (⊥ : SimpleGraph (Fin W))
      let emptyLayer := fkRectBoundaryLayerGraph hW layer.1 priorState
        fkRectBoundaryEmptyLayer
      have hbase : ∀ x y : FKRectLayerVertex W,
          expandedGraph.Reachable (fkRectStripLayerEmbed n x)
              (fkRectStripLayerEmbed n y) ↔
            emptyLayer.Reachable x y := by
        exact fkRectStripExpanded_reachable_iff hW n priorLayers layer.1
          (fun x y => fkRectStrip_boundary_reachable_iff
            hW n priorLayers x y)
      have hcross := finiteBoundaryEdgeRun_component_cross_sum
        (fkRectStripLayerEmbed n) expandedGraph emptyLayer hbase
        (fkRectBoundaryOpenLayerEdges hW layer.1 layer.2)
      have hExpanded :
          Nat.card expandedGraph.ConnectedComponent =
            fkRectStripClosedCount hW n priorLayers +
              Nat.card priorState.ConnectedComponent + W := by
        rw [simpleGraph_card_components_sum]
        change Nat.card priorGraph.ConnectedComponent +
            Nat.card (⊥ : SimpleGraph (Fin W)).ConnectedComponent = _
        rw [ih priorLayers, StatMech.Lattice.card_components_bot, Nat.card_fin]
      have hEmpty :
          Nat.card emptyLayer.ConnectedComponent =
            Nat.card priorState.ConnectedComponent + W := by
        rw [Nat.card_eq_fintype_card,
          fkRectBoundaryEmptyLayer_component_count hW layer.1 priorState
            (fkRectStripState_isConnectivity hW n priorLayers),
          ← Nat.card_eq_fintype_card]
      have hFull :
          Nat.card (fkRectBoundaryLayerGraph hW layer.1 priorState
            layer.2).ConnectedComponent =
            fkRectBoundaryLayerClosedCount hW layer.1 priorState layer.2 +
              Nat.card (fkRectBoundaryLayerOutput hW layer.1 priorState
                layer.2).ConnectedComponent := by
        rw [Nat.card_eq_fintype_card,
          fkRectBoundaryLayer_component_count,
          ← Nat.card_eq_fintype_card]
      have hLayerGraph : finiteBoundaryEdgeRun id emptyLayer
          (fkRectBoundaryOpenLayerEdges hW layer.1 layer.2) =
            fkRectBoundaryLayerGraph hW layer.1 priorState layer.2 := by
        dsimp only [emptyLayer, fkRectBoundaryEmptyLayer]
        exact (fkRectBoundaryLayerGraph_eq_edgeRun hW layer.1 priorState
          layer.2).symm
      have hStripGraph : finiteBoundaryEdgeRun (fkRectStripLayerEmbed n)
          expandedGraph (fkRectBoundaryOpenLayerEdges hW layer.1 layer.2) =
            fkRectStripGraph hW (n + 1) layers := by
        rfl
      rw [hLayerGraph, hStripGraph] at hcross
      have hcross' :
          (fkRectStripClosedCount hW n priorLayers +
              Nat.card priorState.ConnectedComponent + W) +
            (fkRectBoundaryLayerClosedCount hW layer.1 priorState layer.2 +
              Nat.card (fkRectBoundaryLayerOutput hW layer.1 priorState
                layer.2).ConnectedComponent) =
          (Nat.card priorState.ConnectedComponent + W) +
            Nat.card (fkRectStripGraph hW (n + 1) layers).ConnectedComponent := by
        rw [← hExpanded, ← hFull, ← hEmpty]
        exact hcross
      change Nat.card (fkRectStripGraph hW (n + 1) layers).ConnectedComponent =
        (fkRectStripClosedCount hW n priorLayers +
          fkRectBoundaryLayerClosedCount hW layer.1 priorState layer.2) +
        Nat.card (fkRectBoundaryLayerOutput hW layer.1 priorState
          layer.2).ConnectedComponent
      omega

theorem fkRectBoundaryRunState_append
    {W : Nat} (hW : 0 < W) (state : FKRectBoundaryState W)
    (left right : List (Bool × (Bool × Fin W -> Bool))) :
    fkRectBoundaryRunState hW state (left ++ right) =
      fkRectBoundaryRunState hW
        (fkRectBoundaryRunState hW state left) right := by
  induction left generalizing state with
  | nil => rfl
  | cons layer left ih =>
      simp only [List.cons_append, fkRectBoundaryRunState]
      exact ih _

theorem fkRectBoundaryRunClosedCount_append
    {W : Nat} (hW : 0 < W) (state : FKRectBoundaryState W)
    (left right : List (Bool × (Bool × Fin W -> Bool))) :
    fkRectBoundaryRunClosedCount hW state (left ++ right) =
      fkRectBoundaryRunClosedCount hW state left +
        fkRectBoundaryRunClosedCount hW
          (fkRectBoundaryRunState hW state left) right := by
  induction left generalizing state with
  | nil => simp [fkRectBoundaryRunClosedCount, fkRectBoundaryRunState]
  | cons layer left ih =>
      simp only [List.cons_append, fkRectBoundaryRunClosedCount,
        fkRectBoundaryRunState]
      rw [ih]
      omega

theorem fkRectStripState_eq_runState
    {W : Nat} (hW : 0 < W) (n : Nat)
    (layers : Fin n -> Bool × (Bool × Fin W -> Bool)) :
    fkRectStripState hW n layers =
      fkRectBoundaryRunState hW (fkRectBoundaryInitialState W)
        (List.ofFn layers) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.ofFn_succ_last,
        fkRectBoundaryRunState_append, ← ih]
      rfl

theorem fkRectStripClosedCount_eq_runClosedCount
    {W : Nat} (hW : 0 < W) (n : Nat)
    (layers : Fin n -> Bool × (Bool × Fin W -> Bool)) :
    fkRectStripClosedCount hW n layers =
      fkRectBoundaryRunClosedCount hW (fkRectBoundaryInitialState W)
        (List.ofFn layers) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.ofFn_succ_last,
        fkRectBoundaryRunClosedCount_append, ← ih,
        ← fkRectStripState_eq_runState]
      rfl




def fkRectStripSuccEquiv (W n : Nat) :
    (Fin W × Fin (n + 1)) ⊕ Fin W ≃ Fin W × Fin (n + 2) where
  toFun
    | Sum.inl z => (z.1, z.2.castSucc)
    | Sum.inr x => (x, Fin.last (n + 1))
  invFun z := Fin.lastCases (Sum.inr z.1)
    (fun y => Sum.inl (z.1, y)) z.2
  left_inv z := by
    cases z with
    | inl z => simp
    | inr x => simp
  right_inv z := by
    rcases z with ⟨x, y⟩
    refine Fin.lastCases ?_ (fun i => ?_) y
    · simp
    · simp


def fkRectStripVertexEquiv (W : Nat) :
    (n : Nat) -> FKRectStripVertex W n ≃ Fin W × Fin (n + 1)
  | 0 =>
      { toFun := fun x => (x, 0)
        invFun := fun z => z.1
        left_inv := by intro x; rfl
        right_inv := by
          rintro ⟨x, y⟩
          apply Prod.ext
          · rfl
          · exact (Fin.eq_zero y).symm }
  | n + 1 =>
      (Equiv.sumCongr (fkRectStripVertexEquiv W n)
        (Equiv.refl (Fin W))).trans (fkRectStripSuccEquiv W n)

@[simp] theorem fkRectStripVertexEquiv_inl
    {W n : Nat} (v : FKRectStripVertex W n) :
    fkRectStripVertexEquiv W (n + 1) (Sum.inl v) =
      ((fkRectStripVertexEquiv W n v).1,
        (fkRectStripVertexEquiv W n v).2.castSucc) := rfl

@[simp] theorem fkRectStripVertexEquiv_inr
    {W n : Nat} (x : Fin W) :
    fkRectStripVertexEquiv W (n + 1) (Sum.inr x) =
      (x, Fin.last (n + 1)) := rfl

@[simp] theorem fkRectStripVertexEquiv_initial
    {W : Nat} (n : Nat) (x : Fin W) :
    fkRectStripVertexEquiv W n (fkRectStripInitial n x) = (x, 0) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fkRectStripInitial, ih]

@[simp] theorem fkRectStripVertexEquiv_current
    {W : Nat} (n : Nat) (x : Fin W) :
    fkRectStripVertexEquiv W n (fkRectStripCurrent n x) =
      (x, Fin.last n) := by
  cases n with
  | zero =>
      apply Prod.ext
      · rfl
      · exact Fin.eq_zero _
  | succ n => rfl

@[simp] theorem fkRectStripVertexEquiv_boundary
    {W : Nat} (n : Nat) (u : Bool × Fin W) :
    fkRectStripVertexEquiv W n (fkRectStripBoundary n u) =
      if u.1 then (u.2, Fin.last n) else (u.2, 0) := by
  cases u with
  | mk b x => cases b <;> simp [fkRectStripBoundary]



def fkRectCoordinateLayerEdgeEndpoints {W n : Nat} (hW : 0 < W)
    (i : Fin n) (evenRow : Bool) (a : Bool × Fin W) :
    (Fin W × Fin (n + 1)) × (Fin W × Fin (n + 1)) :=
  if a.1 then
    ((a.2, i.castSucc), (a.2, i.succ))
  else if evenRow then
    ((SixVertexArrows.cyclicPred hW a.2, i.castSucc), (a.2, i.succ))
  else
    ((a.2, i.castSucc),
      (SixVertexArrows.cyclicPred hW a.2, i.succ))

theorem fkRectCoordinateLayerEdgeEndpoints_last
    {W : Nat} (hW : 0 < W) (n : Nat) (evenRow : Bool)
    (a : Bool × Fin W) :
    Prod.map (fkRectStripVertexEquiv W (n + 1))
        (fkRectStripVertexEquiv W (n + 1))
        (Prod.map (fkRectStripLayerEmbed n) (fkRectStripLayerEmbed n)
          (fkRectLayerEdgeEndpoints hW evenRow a)) =
      fkRectCoordinateLayerEdgeEndpoints hW (Fin.last n) evenRow a := by
  rcases a with ⟨dir, x⟩
  cases dir <;> cases evenRow <;>
    simp [fkRectLayerEdgeEndpoints, fkRectCoordinateLayerEdgeEndpoints,
      fkRectStripLayerEmbed, fkRectLayerInitialRole,
      fkRectLayerOldRole, fkRectLayerNewRole]

def fkRectCoordinateLayerEdge {W n : Nat} (hW : 0 < W)
    (i : Fin n) (evenRow : Bool) (a : Bool × Fin W) :
    Sym2 (Fin W × Fin (n + 1)) :=
  s((fkRectCoordinateLayerEdgeEndpoints hW i evenRow a).1,
    (fkRectCoordinateLayerEdgeEndpoints hW i evenRow a).2)

theorem fin_exists_castSucc_or_last {n : Nat} {P : Fin (n + 1) -> Prop} :
    (∃ i, P i) ↔ (∃ i : Fin n, P i.castSucc) ∨ P (Fin.last n) := by
  constructor
  · rintro ⟨i, hi⟩
    revert hi
    refine Fin.lastCases ?_ (fun j hj => ?_) i
    · exact Or.inr
    · exact Or.inl ⟨j, hj⟩
  · rintro (⟨i, hi⟩ | hi)
    · exact ⟨i.castSucc, hi⟩
    · exact ⟨Fin.last n, hi⟩

theorem fkRectCoordinateLayerEdge_castSucc
    {W n : Nat} (hW : 0 < W) (i : Fin n) (evenRow : Bool)
    (a : Bool × Fin W) :
    fkRectCoordinateLayerEdge hW i.castSucc evenRow a =
      Sym2.map (fun z : Fin W × Fin (n + 1) => (z.1, z.2.castSucc))
        (fkRectCoordinateLayerEdge hW i evenRow a) := by
  rcases a with ⟨dir, x⟩
  cases dir <;> cases evenRow <;>
    rfl

theorem fkRectCoordinateLayerEdge_last
    {W : Nat} (hW : 0 < W) (n : Nat) (evenRow : Bool)
    (a : Bool × Fin W) :
    fkRectCoordinateLayerEdge hW (Fin.last n) evenRow a =
      Sym2.map (fkRectStripVertexEquiv W (n + 1))
        s(fkRectStripLayerEmbed n
            (fkRectLayerEdgeEndpoints hW evenRow a).1,
          fkRectStripLayerEmbed n
            (fkRectLayerEdgeEndpoints hW evenRow a).2) := by
  rw [Sym2.map_pair_eq]
  exact congrArg (fun e => s(e.1, e.2))
    (fkRectCoordinateLayerEdgeEndpoints_last hW n evenRow a).symm

theorem sym2_map_eq_map_iff_of_injective
    {A B : Type*} (f : A -> B) (hf : Function.Injective f)
    (e e' : Sym2 A) : Sym2.map f e = Sym2.map f e' ↔ e = e' := by
  constructor
  · intro h
    induction e using Sym2.inductionOn with
    | _ a b =>
      induction e' using Sym2.inductionOn with
      | _ c d =>
        simp only [Sym2.map_pair_eq, Sym2.eq_iff] at h ⊢
        rcases h with h | h
        · exact Or.inl ⟨hf h.1, hf h.2⟩
        · exact Or.inr ⟨hf h.1, hf h.2⟩
  · exact congrArg (Sym2.map f)

def fkRectStripRowCast {W n : Nat} :
    Fin W × Fin (n + 1) -> Fin W × Fin (n + 2) := fun z =>
  (z.1, z.2.castSucc)

theorem fkRectStripRowCast_injective {W n : Nat} :
    Function.Injective (fkRectStripRowCast (W := W) (n := n)) := by
  rintro ⟨x, i⟩ ⟨y, j⟩ h
  simp only [fkRectStripRowCast, Prod.mk.injEq] at h ⊢
  exact ⟨h.1, Fin.castSucc_inj.mp h.2⟩

theorem sym2_fkRectStripRowCast_ne_cast_last
    {W n : Nat} (e : Sym2 (Fin W × Fin (n + 1)))
    (z : Fin W × Fin (n + 1)) (x : Fin W) :
    Sym2.map fkRectStripRowCast e ≠
      s(fkRectStripRowCast z, (x, Fin.last (n + 1))) := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    rw [Sym2.map_pair_eq]
    intro heq
    rw [Sym2.eq_iff] at heq
    rcases heq with h | h
    · exact Fin.castSucc_ne_last _ (congrArg Prod.snd h.2)
    · exact Fin.castSucc_ne_last _ (congrArg Prod.snd h.1)

theorem sym2_fkRectStripRowCast_ne_last_last
    {W n : Nat} (e : Sym2 (Fin W × Fin (n + 1))) (x y : Fin W) :
    Sym2.map fkRectStripRowCast e ≠
      s((x, Fin.last (n + 1)), (y, Fin.last (n + 1))) := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    rw [Sym2.map_pair_eq]
    intro heq
    rw [Sym2.eq_iff] at heq
    rcases heq with h | h
    · exact Fin.castSucc_ne_last _ (congrArg Prod.snd h.1)
    · exact Fin.castSucc_ne_last _ (congrArg Prod.snd h.1)



theorem fkRectStripGraph_adj_iff_coordinateEdge
    {W : Nat} (hW : 0 < W) (n : Nat)
    (layers : Fin n -> Bool × (Bool × Fin W -> Bool))
    (u v : FKRectStripVertex W n) :
    (fkRectStripGraph hW n layers).Adj u v ↔
      u ≠ v ∧ ∃ i : Fin n, ∃ a : Bool × Fin W,
        (layers i).2 a = true ∧
          fkRectCoordinateLayerEdge hW i (layers i).1 a =
            s(fkRectStripVertexEquiv W n u,
              fkRectStripVertexEquiv W n v) := by
  induction n with
  | zero => simp [fkRectStripGraph]
  | succ n ih =>
      let priorLayers : Fin n -> Bool × (Bool × Fin W -> Bool) :=
        fun i => layers i.castSucc
      let rowCast : Fin W × Fin (n + 1) -> Fin W × Fin (n + 2) :=
        fkRectStripRowCast
      have hrowCast : Function.Injective rowCast :=
        fkRectStripRowCast_injective
      constructor
      · intro hadj
        have hne : u ≠ v := fun huv =>
          (fkRectStripGraph hW (n + 1) layers).loopless.irrefl u
            (huv ▸ hadj)
        refine ⟨hne, ?_⟩
        rw [fkRectStripGraph_succ_adj_iff] at hadj
        rcases hadj with hprior | ⟨a, hopen, hedge⟩
        · cases u with
          | inl u =>
              cases v with
              | inl v =>
                  have hp : (fkRectStripGraph hW n priorLayers).Adj u v := by
                    simpa only [SimpleGraph.sum_adj] using hprior
                  obtain ⟨_, i, a, hopen, hcoord⟩ :=
                    (ih priorLayers u v).1 hp
                  refine ⟨i.castSucc, a, hopen, ?_⟩
                  rw [fkRectCoordinateLayerEdge_castSucc]
                  simpa only [Sym2.map_pair_eq,
                    fkRectStripVertexEquiv_inl] using
                    congrArg (Sym2.map rowCast) hcoord
              | inr v => simp only [SimpleGraph.sum_adj] at hprior
          | inr u =>
              cases v with
              | inl v => simp only [SimpleGraph.sum_adj] at hprior
              | inr v => simp only [SimpleGraph.sum_adj,
                  SimpleGraph.bot_adj] at hprior
        · refine ⟨Fin.last n, a, hopen, ?_⟩
          rw [fkRectCoordinateLayerEdge_last]
          have hedge' := (SimpleGraph.adj_edge _ _).1 hedge
          simpa only [Sym2.map_pair_eq] using
            congrArg (Sym2.map (fkRectStripVertexEquiv W (n + 1)))
              hedge'.1
      · rintro ⟨hne, i, a, hopen, hcoord⟩
        rw [fkRectStripGraph_succ_adj_iff]
        revert a
        refine Fin.lastCases ?_ (fun j => ?_) i
        · intro a hopen hcoord
          refine Or.inr ⟨a, hopen, ?_⟩
          apply (SimpleGraph.adj_edge _ _).2
          refine ⟨?_, hne⟩
          rw [fkRectCoordinateLayerEdge_last] at hcoord
          apply (sym2_map_eq_map_iff_of_injective
            (fkRectStripVertexEquiv W (n + 1))
            (fkRectStripVertexEquiv W (n + 1)).injective _ _).1
          simpa only [Sym2.map_pair_eq] using hcoord
        · intro a hopen hcoord
          rw [fkRectCoordinateLayerEdge_castSucc] at hcoord
          cases u with
          | inl u =>
              cases v with
              | inl v =>
                  refine Or.inl ?_
                  change (fkRectStripGraph hW n priorLayers).Adj u v
                  apply (ih priorLayers u v).2
                  refine ⟨fun huv => hne (congrArg Sum.inl huv),
                    j, a, hopen, ?_⟩
                  apply (sym2_map_eq_map_iff_of_injective
                    rowCast hrowCast _ _).1
                  simpa only [Sym2.map_pair_eq,
                    fkRectStripVertexEquiv_inl] using hcoord
              | inr v =>
                  exfalso
                  exact sym2_fkRectStripRowCast_ne_cast_last
                    (fkRectCoordinateLayerEdge hW j
                      (layers j.castSucc).1 a)
                    (fkRectStripVertexEquiv W n u) v (by
                      simpa only [fkRectStripVertexEquiv_inl,
                        fkRectStripVertexEquiv_inr] using hcoord)
          | inr u =>
              cases v with
              | inl v =>
                  exfalso
                  exact sym2_fkRectStripRowCast_ne_cast_last
                    (fkRectCoordinateLayerEdge hW j
                      (layers j.castSucc).1 a)
                    (fkRectStripVertexEquiv W n v) u (by
                      simpa only [fkRectStripVertexEquiv_inl,
                        fkRectStripVertexEquiv_inr, Sym2.eq_swap]
                        using hcoord)
              | inr v =>
                  exfalso
                  exact sym2_fkRectStripRowCast_ne_last_last
                    (fkRectCoordinateLayerEdge hW j
                      (layers j.castSucc).1 a) u v (by
                      simpa only [fkRectStripVertexEquiv_inr] using hcoord)



def fkRectBoundarySeamEdgeEndpoints {W : Nat} (hW : 0 < W)
    (a : Bool × Fin W) :
    (Bool × Fin W) × (Bool × Fin W) :=
  if a.1 then
    ((true, a.2), (false, a.2))
  else
    ((true, SixVertexArrows.cyclicPred hW a.2), (false, a.2))

theorem fkRectBoundarySeamEdgeEndpoints_ne {W : Nat} (hW : 0 < W)
    (a : Bool × Fin W) :
    (fkRectBoundarySeamEdgeEndpoints hW a).1 ≠
      (fkRectBoundarySeamEdgeEndpoints hW a).2 := by
  cases a with
  | mk dir x => cases dir <;> simp [fkRectBoundarySeamEdgeEndpoints]


def fkRectBoundarySeamGraph {W : Nat} (hW : 0 < W)
    (state : FKRectBoundaryState W)
    (eta : Bool × Fin W -> Bool) : SimpleGraph (Bool × Fin W) where
  Adj u v := state.Adj u v ∨
    ∃ a, eta a = true ∧
      (((fkRectBoundarySeamEdgeEndpoints hW a).1 = u ∧
          (fkRectBoundarySeamEdgeEndpoints hW a).2 = v) ∨
        ((fkRectBoundarySeamEdgeEndpoints hW a).1 = v ∧
          (fkRectBoundarySeamEdgeEndpoints hW a).2 = u))
  symm := by
    rintro u v (hstate | hedge)
    · exact Or.inl hstate.symm
    · obtain ⟨a, ha, huv | huv⟩ := hedge
      · exact Or.inr ⟨a, ha, Or.inr ⟨huv.1, huv.2⟩⟩
      · exact Or.inr ⟨a, ha, Or.inl ⟨huv.1, huv.2⟩⟩
  loopless := ⟨by
    intro u huu
    rcases huu with hstate | hedge
    · exact state.loopless.irrefl u hstate
    · obtain ⟨a, _, huu | huu⟩ := hedge
      · exact fkRectBoundarySeamEdgeEndpoints_ne hW a
          (huu.1.trans huu.2.symm)
      · exact fkRectBoundarySeamEdgeEndpoints_ne hW a
          (huu.2.trans huu.1.symm).symm⟩


def fkRectBoundaryOpenSeamEdges {W : Nat} (hW : 0 < W)
    (eta : Bool × Fin W -> Bool) :
    List ((Bool × Fin W) × (Bool × Fin W)) :=
  (fkRectBoundaryOpenLayerIndices eta).map
    (fkRectBoundarySeamEdgeEndpoints hW)

theorem fkRectBoundarySeamGraph_eq_edgeRun
    {W : Nat} (hW : 0 < W) (state : FKRectBoundaryState W)
    (eta : Bool × Fin W -> Bool) :
    fkRectBoundarySeamGraph hW state eta =
      finiteBoundaryEdgeRun id state
        (fkRectBoundaryOpenSeamEdges hW eta) := by
  classical
  ext u v
  rw [finiteBoundaryEdgeRun_adj_iff]
  unfold fkRectBoundarySeamGraph fkRectBoundaryOpenSeamEdges
    fkRectBoundaryOpenLayerIndices
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter,
    Finset.mem_univ, true_and, SimpleGraph.edge_adj, id_eq]
  constructor
  · rintro (hstate | ⟨a, ha, huv⟩)
    · exact Or.inl hstate
    · have hne : u ≠ v := by
        intro huvEq
        apply fkRectBoundarySeamEdgeEndpoints_ne hW a
        rcases huv with huv | huv
        · exact huv.1.trans (huvEq.trans huv.2.symm)
        · exact (huv.2.trans (huvEq.trans huv.1.symm)).symm
      refine Or.inr ⟨fkRectBoundarySeamEdgeEndpoints hW a,
        ⟨a, ha, rfl⟩, ⟨?_, hne⟩⟩
      rcases huv with huv | huv
      · exact Or.inl ⟨huv.1.symm, huv.2.symm⟩
      · exact Or.inr ⟨huv.2.symm, huv.1.symm⟩
  · rintro (hstate | ⟨e, ⟨a, ha, rfl⟩, hedge⟩)
    · exact Or.inl hstate
    · refine Or.inr ⟨a, ha, ?_⟩
      rcases hedge.1 with hedge | hedge
      · exact Or.inl ⟨hedge.1.symm, hedge.2.symm⟩
      · exact Or.inr ⟨hedge.2.symm, hedge.1.symm⟩



def fkRectStripSeamGraph {W : Nat} (hW : 0 < W) (n : Nat)
    (layers : Fin n -> Bool × (Bool × Fin W -> Bool))
    (eta : Bool × Fin W -> Bool) : SimpleGraph (FKRectStripVertex W n) :=
  finiteBoundaryEdgeRun (fkRectStripBoundary n)
    (fkRectStripGraph hW n layers) (fkRectBoundaryOpenSeamEdges hW eta)


def fkRectCoordinateSeamEdge {W n : Nat} (hW : 0 < W)
    (a : Bool × Fin W) : Sym2 (Fin W × Fin (n + 1)) :=
  if a.1 then
    s((a.2, Fin.last n), (a.2, 0))
  else
    s((SixVertexArrows.cyclicPred hW a.2, Fin.last n), (a.2, 0))

theorem fkRectCoordinateSeamEdge_eq_map
    {W : Nat} (hW : 0 < W) (n : Nat) (a : Bool × Fin W) :
    fkRectCoordinateSeamEdge (n := n) hW a =
      Sym2.map (fkRectStripVertexEquiv W n)
        s(fkRectStripBoundary n (fkRectBoundarySeamEdgeEndpoints hW a).1,
          fkRectStripBoundary n
            (fkRectBoundarySeamEdgeEndpoints hW a).2) := by
  rw [Sym2.map_pair_eq]
  rcases a with ⟨dir, x⟩
  cases dir <;> simp [fkRectCoordinateSeamEdge,
    fkRectBoundarySeamEdgeEndpoints]

theorem fkRectStripSeamGraph_adj_iff
    {W : Nat} (hW : 0 < W) (n : Nat)
    (layers : Fin n -> Bool × (Bool × Fin W -> Bool))
    (eta : Bool × Fin W -> Bool) (u v : FKRectStripVertex W n) :
    (fkRectStripSeamGraph hW n layers eta).Adj u v ↔
      (fkRectStripGraph hW n layers).Adj u v ∨
      ∃ a : Bool × Fin W, eta a = true ∧
        (SimpleGraph.edge
          (fkRectStripBoundary n
            (fkRectBoundarySeamEdgeEndpoints hW a).1)
          (fkRectStripBoundary n
            (fkRectBoundarySeamEdgeEndpoints hW a).2)).Adj u v := by
  rw [fkRectStripSeamGraph, finiteBoundaryEdgeRun_adj_iff]
  unfold fkRectBoundaryOpenSeamEdges fkRectBoundaryOpenLayerIndices
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter,
    Finset.mem_univ, true_and]
  aesop

theorem fkRectStripSeamGraph_adj_iff_coordinateEdge
    {W : Nat} (hW : 0 < W) (n : Nat)
    (layers : Fin n -> Bool × (Bool × Fin W -> Bool))
    (eta : Bool × Fin W -> Bool) (u v : FKRectStripVertex W n) :
    (fkRectStripSeamGraph hW n layers eta).Adj u v ↔
      u ≠ v ∧
        ((∃ i : Fin n, ∃ a : Bool × Fin W,
          (layers i).2 a = true ∧
            fkRectCoordinateLayerEdge hW i (layers i).1 a =
              s(fkRectStripVertexEquiv W n u,
                fkRectStripVertexEquiv W n v)) ∨
        ∃ a : Bool × Fin W, eta a = true ∧
          fkRectCoordinateSeamEdge (n := n) hW a =
            s(fkRectStripVertexEquiv W n u,
              fkRectStripVertexEquiv W n v)) := by
  rw [fkRectStripSeamGraph_adj_iff,
    fkRectStripGraph_adj_iff_coordinateEdge]
  constructor
  · rintro (⟨hne, hnonSeam⟩ | ⟨a, hopen, hedge⟩)
    · exact ⟨hne, Or.inl hnonSeam⟩
    · have hedge' := (SimpleGraph.adj_edge _ _).1 hedge
      refine ⟨hedge'.2, Or.inr ⟨a, hopen, ?_⟩⟩
      rw [fkRectCoordinateSeamEdge_eq_map]
      simpa only [Sym2.map_pair_eq] using
        congrArg (Sym2.map (fkRectStripVertexEquiv W n)) hedge'.1
  · rintro ⟨hne, hnonSeam | ⟨a, hopen, hcoord⟩⟩
    · exact Or.inl ⟨hne, hnonSeam⟩
    · refine Or.inr ⟨a, hopen, ?_⟩
      apply (SimpleGraph.adj_edge _ _).2
      refine ⟨?_, hne⟩
      rw [fkRectCoordinateSeamEdge_eq_map] at hcoord
      apply (sym2_map_eq_map_iff_of_injective
        (fkRectStripVertexEquiv W n)
        (fkRectStripVertexEquiv W n).injective _ _).1
      simpa only [Sym2.map_pair_eq] using hcoord

theorem fkRectStripSeamGraph_component_count
    {W : Nat} (hW : 0 < W) (n : Nat)
    (layers : Fin n -> Bool × (Bool × Fin W -> Bool))
    (eta : Bool × Fin W -> Bool) :
    Nat.card (fkRectStripSeamGraph hW n layers eta).ConnectedComponent =
      fkRectStripClosedCount hW n layers +
        Nat.card (fkRectBoundarySeamGraph hW
          (fkRectStripState hW n layers) eta).ConnectedComponent := by
  have hcross := finiteBoundaryEdgeRun_component_cross_sum
    (fkRectStripBoundary n) (fkRectStripGraph hW n layers)
    (fkRectStripState hW n layers)
    (fun u v => fkRectStrip_boundary_reachable_iff hW n layers u v)
    (fkRectBoundaryOpenSeamEdges hW eta)
  have hstrip := fkRectStrip_component_count hW n layers
  have hseam := fkRectBoundarySeamGraph_eq_edgeRun hW
    (fkRectStripState hW n layers) eta
  have hstripSeam : finiteBoundaryEdgeRun (fkRectStripBoundary n)
      (fkRectStripGraph hW n layers) (fkRectBoundaryOpenSeamEdges hW eta) =
        fkRectStripSeamGraph hW n layers eta := rfl
  rw [← hseam, hstripSeam] at hcross
  have hcross' :
      (fkRectStripClosedCount hW n layers +
          Nat.card (fkRectStripState hW n layers).ConnectedComponent) +
        Nat.card (fkRectBoundarySeamGraph hW
          (fkRectStripState hW n layers) eta).ConnectedComponent =
      Nat.card (fkRectStripState hW n layers).ConnectedComponent +
        Nat.card (fkRectStripSeamGraph hW n layers eta).ConnectedComponent := by
    rw [← hstrip]
    exact hcross
  omega



def fkRectBoundarySeamWeight {W : Nat} (hW : 0 < W) (q : Real)
    (state : FKRectBoundaryState W)
    (eta : Bool × Fin W -> Bool) : Real :=
  Real.sqrt q ^ fkRectBoundaryLayerOpenCount eta *
    q ^ Fintype.card (fkRectBoundarySeamGraph hW state eta).ConnectedComponent


def fkRectBoundarySeamFunctional {W : Nat} (hW : 0 < W) (q : Real)
    (state : FKRectBoundaryState W) : Real :=
  ∑ eta : Bool × Fin W -> Bool,
    fkRectBoundarySeamWeight hW q state eta


def fkRectConfigurationFinalBoundaryState (R : FKRectTorus)
    (omega : R.Configuration) : FKRectBoundaryState R.width :=
  fkRectBoundaryRunState R.width_pos (fkRectBoundaryInitialState R.width)
    (fkRectConfigurationNonSeamLayers R omega)


def fkRectBoundaryTransferClusterCount (R : FKRectTorus)
    (omega : R.Configuration) : Nat :=
  fkRectBoundaryRunClosedCount R.width_pos
      (fkRectBoundaryInitialState R.width)
      (fkRectConfigurationNonSeamLayers R omega) +
    Fintype.card
      (fkRectBoundarySeamGraph R.width_pos
        (fkRectConfigurationFinalBoundaryState R omega)
        (fkRectConfigurationLayer R omega
          (fkRectBoundarySeamRow R))).ConnectedComponent



def fkRectBoundaryTransferCoefficient (R : FKRectTorus) (q : Real)
    (omega : R.Configuration) : Real :=
  fkRectBoundaryRunWeight R.width_pos q (fkRectBoundaryInitialState R.width)
      (fkRectConfigurationNonSeamLayers R omega) *
    fkRectBoundarySeamWeight R.width_pos q
      (fkRectConfigurationFinalBoundaryState R omega)
      (fkRectConfigurationLayer R omega (fkRectBoundarySeamRow R))




theorem fkRectBoundaryTransferCoefficient_eq
    (R : FKRectTorus) (q : Real) (omega : R.Configuration) :
    fkRectBoundaryTransferCoefficient R q omega =
      Real.sqrt q ^ fkRectOpenEdgeCount R omega *
        q ^ fkRectBoundaryTransferClusterCount R omega := by
  rw [fkRectBoundaryTransferCoefficient, fkRectBoundaryRunWeight_eq]
  unfold fkRectBoundarySeamWeight fkRectBoundaryTransferClusterCount
  rw [fkRectOpenEdgeCount_eq_run_add_seam, pow_add, pow_add]
  ring


def fkRectConfigurationNonSeamLayerFn (R : FKRectTorus)
    (omega : R.Configuration) :
    Fin (R.height - 1) -> Bool × (Bool × Fin R.width -> Bool) := fun i =>
  let y := fkRectBoundaryNonSeamRow R i
  (decide (Even y.val), fkRectConfigurationLayer R omega y)

@[simp] theorem fkRectConfigurationNonSeamLayers_eq_ofFn
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectConfigurationNonSeamLayers R omega =
      List.ofFn (fkRectConfigurationNonSeamLayerFn R omega) := rfl



def fkRectConfigurationScheduleEquiv (R : FKRectTorus) :
    R.Configuration ≃
      (Bool × Fin R.width -> Bool) ×
        (Fin (R.height - 1) -> Bool × Fin R.width -> Bool) :=
  (fkRectConfigurationLayersEquiv R).trans
    ((Equiv.arrowCongr (finCongr (Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr R.height_pos.ne'))).symm
      (Equiv.refl _)).trans
    ((Equiv.arrowCongr (finSuccEquiv (R.height - 1))
      (Equiv.refl _)).trans Equiv.piOptionEquivProd))

@[simp] theorem fkRectConfigurationScheduleEquiv_fst
    (R : FKRectTorus) (omega : R.Configuration) :
    (fkRectConfigurationScheduleEquiv R omega).1 =
      fkRectConfigurationLayer R omega (fkRectBoundarySeamRow R) := by
  funext a
  rfl

@[simp] theorem fkRectConfigurationScheduleEquiv_snd
    (R : FKRectTorus) (omega : R.Configuration)
    (i : Fin (R.height - 1)) :
    (fkRectConfigurationScheduleEquiv R omega).2 i =
      fkRectConfigurationLayer R omega (fkRectBoundaryNonSeamRow R i) := by
  funext a
  rfl

@[simp] theorem fkRectConfigurationScheduleEquiv_symm_seam
    (R : FKRectTorus) (seam : Bool × Fin R.width -> Bool)
    (layers : Fin (R.height - 1) -> Bool × Fin R.width -> Bool) :
    fkRectConfigurationLayer R
        ((fkRectConfigurationScheduleEquiv R).symm (seam, layers))
        (fkRectBoundarySeamRow R) = seam := by
  have h := congrArg Prod.fst
    ((fkRectConfigurationScheduleEquiv R).apply_symm_apply (seam, layers))
  change (fkRectConfigurationScheduleEquiv R
    ((fkRectConfigurationScheduleEquiv R).symm (seam, layers))).1 = seam at h
  rw [fkRectConfigurationScheduleEquiv_fst] at h
  exact h

@[simp] theorem fkRectConfigurationScheduleEquiv_symm_nonSeam
    (R : FKRectTorus) (seam : Bool × Fin R.width -> Bool)
    (layers : Fin (R.height - 1) -> Bool × Fin R.width -> Bool)
    (i : Fin (R.height - 1)) :
    fkRectConfigurationLayer R
        ((fkRectConfigurationScheduleEquiv R).symm (seam, layers))
        (fkRectBoundaryNonSeamRow R i) = layers i := by
  have h := congrArg (fun p => p.2 i)
    ((fkRectConfigurationScheduleEquiv R).apply_symm_apply (seam, layers))
  change (fkRectConfigurationScheduleEquiv R
    ((fkRectConfigurationScheduleEquiv R).symm (seam, layers))).2 i =
      layers i at h
  rw [fkRectConfigurationScheduleEquiv_snd] at h
  exact h

theorem fkRectBoundaryTransferCoefficient_schedule_symm
    (R : FKRectTorus) (q : Real)
    (seam : Bool × Fin R.width -> Bool)
    (layers : Fin (R.height - 1) -> Bool × Fin R.width -> Bool) :
    fkRectBoundaryTransferCoefficient R q
        ((fkRectConfigurationScheduleEquiv R).symm (seam, layers)) =
      fkRectBoundaryRunWeight R.width_pos q
          (fkRectBoundaryInitialState R.width)
          (List.ofFn fun i : Fin (R.height - 1) =>
            (decide (Even (fkRectBoundaryNonSeamRow R i).val), layers i)) *
        fkRectBoundarySeamWeight R.width_pos q
          (fkRectBoundaryRunState R.width_pos
            (fkRectBoundaryInitialState R.width)
            (List.ofFn fun i : Fin (R.height - 1) =>
              (decide (Even (fkRectBoundaryNonSeamRow R i).val), layers i)))
          seam := by
  simp [fkRectBoundaryTransferCoefficient,
    fkRectConfigurationFinalBoundaryState,
    fkRectConfigurationNonSeamLayers]

theorem sum_fkRectBoundaryTransferCoefficient_eq_layerSum
    (R : FKRectTorus) (q : Real) :
    (∑ omega : R.Configuration,
      fkRectBoundaryTransferCoefficient R q omega) =
    ∑ layers : Fin (R.height - 1) -> Bool × Fin R.width -> Bool,
      fkRectBoundaryRunWeight R.width_pos q
          (fkRectBoundaryInitialState R.width)
          (List.ofFn fun i : Fin (R.height - 1) =>
            (decide (Even (fkRectBoundaryNonSeamRow R i).val), layers i)) *
        fkRectBoundarySeamFunctional R.width_pos q
          (fkRectBoundaryRunState R.width_pos
            (fkRectBoundaryInitialState R.width)
            (List.ofFn fun i : Fin (R.height - 1) =>
              (decide (Even (fkRectBoundaryNonSeamRow R i).val),
                layers i))) := by
  classical
  calc
    (∑ omega : R.Configuration,
        fkRectBoundaryTransferCoefficient R q omega) =
        ∑ p : (Bool × Fin R.width -> Bool) ×
            (Fin (R.height - 1) -> Bool × Fin R.width -> Bool),
          fkRectBoundaryTransferCoefficient R q
            ((fkRectConfigurationScheduleEquiv R).symm p) := by
              apply Fintype.sum_equiv (fkRectConfigurationScheduleEquiv R)
              intro omega
              simp
    _ = ∑ seam : Bool × Fin R.width -> Bool,
        ∑ layers : Fin (R.height - 1) -> Bool × Fin R.width -> Bool,
          fkRectBoundaryRunWeight R.width_pos q
              (fkRectBoundaryInitialState R.width)
              (List.ofFn fun i : Fin (R.height - 1) =>
                (decide (Even (fkRectBoundaryNonSeamRow R i).val),
                  layers i)) *
            fkRectBoundarySeamWeight R.width_pos q
              (fkRectBoundaryRunState R.width_pos
                (fkRectBoundaryInitialState R.width)
                (List.ofFn fun i : Fin (R.height - 1) =>
                  (decide (Even (fkRectBoundaryNonSeamRow R i).val),
                    layers i))) seam := by
              rw [Fintype.sum_prod_type]
              apply Finset.sum_congr rfl
              intro seam hseam
              apply Finset.sum_congr rfl
              intro layers hlayers
              exact fkRectBoundaryTransferCoefficient_schedule_symm
                R q seam layers
    _ = ∑ layers : Fin (R.height - 1) -> Bool × Fin R.width -> Bool,
        ∑ seam : Bool × Fin R.width -> Bool,
          fkRectBoundaryRunWeight R.width_pos q
              (fkRectBoundaryInitialState R.width)
              (List.ofFn fun i : Fin (R.height - 1) =>
                (decide (Even (fkRectBoundaryNonSeamRow R i).val),
                  layers i)) *
            fkRectBoundarySeamWeight R.width_pos q
              (fkRectBoundaryRunState R.width_pos
                (fkRectBoundaryInitialState R.width)
                (List.ofFn fun i : Fin (R.height - 1) =>
                  (decide (Even (fkRectBoundaryNonSeamRow R i).val),
                    layers i))) seam := by
              rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro layers hlayers
      rw [← Finset.mul_sum]
      rfl


def finFunctionConsEquiv (n : Nat) (A : Type*) :
    (Fin (n + 1) -> A) ≃ A × (Fin n -> A) :=
  (Equiv.arrowCongr (finSuccEquiv n) (Equiv.refl A)).trans
    Equiv.piOptionEquivProd

@[simp] theorem finFunctionConsEquiv_fst
    {n : Nat} {A : Type*} (f : Fin (n + 1) -> A) :
    (finFunctionConsEquiv n A f).1 = f 0 := rfl

@[simp] theorem finFunctionConsEquiv_snd
    {n : Nat} {A : Type*} (f : Fin (n + 1) -> A) (i : Fin n) :
    (finFunctionConsEquiv n A f).2 i = f i.succ := rfl

@[simp] theorem finFunctionConsEquiv_symm_zero
    {n : Nat} {A : Type*} (a : A) (f : Fin n -> A) :
    (finFunctionConsEquiv n A).symm (a, f) 0 = a := rfl

@[simp] theorem finFunctionConsEquiv_symm_succ
    {n : Nat} {A : Type*} (a : A) (f : Fin n -> A) (i : Fin n) :
    (finFunctionConsEquiv n A).symm (a, f) i.succ = f i := rfl


def fkRectBoundaryListCoefficientSum {W : Nat} (hW : 0 < W)
    (q : Real) : FKRectBoundaryState W -> List Bool -> Real
  | state, [] => fkRectBoundarySeamFunctional hW q state
  | state, evenRow :: rows =>
      ∑ eta : Bool × Fin W -> Bool,
        fkRectBoundaryLayerWeight hW q evenRow state eta *
          fkRectBoundaryListCoefficientSum hW q
            (fkRectBoundaryLayerOutput hW evenRow state eta) rows

theorem fkRectBoundaryFiniteLayerSum_eq_listCoefficientSum
    {W : Nat} (hW : 0 < W) (q : Real)
    (state : FKRectBoundaryState W) (n : Nat) (parity : Fin n -> Bool) :
    (∑ layers : Fin n -> Bool × Fin W -> Bool,
      fkRectBoundaryRunWeight hW q state
          (List.ofFn fun i : Fin n => (parity i, layers i)) *
        fkRectBoundarySeamFunctional hW q
          (fkRectBoundaryRunState hW state
            (List.ofFn fun i : Fin n => (parity i, layers i)))) =
      fkRectBoundaryListCoefficientSum hW q state
        (List.ofFn parity) := by
  induction n generalizing state with
  | zero =>
      simp [fkRectBoundaryRunWeight, fkRectBoundaryRunState,
        fkRectBoundaryListCoefficientSum]
  | succ n ih =>
      let A := Bool × Fin W -> Bool
      let split : (Fin (n + 1) -> A) ≃ A × (Fin n -> A) :=
        finFunctionConsEquiv n A
      calc
        (∑ layers : Fin (n + 1) -> A,
          fkRectBoundaryRunWeight hW q state
              (List.ofFn fun i : Fin (n + 1) =>
                (parity i, layers i)) *
            fkRectBoundarySeamFunctional hW q
              (fkRectBoundaryRunState hW state
                (List.ofFn fun i : Fin (n + 1) =>
                  (parity i, layers i)))) =
            ∑ p : A × (Fin n -> A),
              fkRectBoundaryRunWeight hW q state
                  ((parity 0, p.1) :: List.ofFn fun i : Fin n =>
                    (parity i.succ, p.2 i)) *
                fkRectBoundarySeamFunctional hW q
                  (fkRectBoundaryRunState hW state
                    ((parity 0, p.1) :: List.ofFn fun i : Fin n =>
                      (parity i.succ, p.2 i))) := by
                apply Fintype.sum_equiv split
                intro layers
                simp [split, A, List.ofFn_succ]
        _ = ∑ eta : A, ∑ layers : Fin n -> A,
              fkRectBoundaryLayerWeight hW q (parity 0) state eta *
                (fkRectBoundaryRunWeight hW q
                    (fkRectBoundaryLayerOutput hW (parity 0) state eta)
                    (List.ofFn fun i : Fin n =>
                      (parity i.succ, layers i)) *
                  fkRectBoundarySeamFunctional hW q
                    (fkRectBoundaryRunState hW
                      (fkRectBoundaryLayerOutput hW (parity 0) state eta)
                      (List.ofFn fun i : Fin n =>
                        (parity i.succ, layers i)))) := by
                rw [Fintype.sum_prod_type]
                simp only [fkRectBoundaryRunWeight,
                  fkRectBoundaryRunState]
                ring
        _ = ∑ eta : A,
              fkRectBoundaryLayerWeight hW q (parity 0) state eta *
                fkRectBoundaryListCoefficientSum hW q
                  (fkRectBoundaryLayerOutput hW (parity 0) state eta)
                  (List.ofFn fun i : Fin n => parity i.succ) := by
                apply Finset.sum_congr rfl
                intro eta heta
                rw [← ih, Finset.mul_sum]
        _ = fkRectBoundaryListCoefficientSum hW q state
              (List.ofFn parity) := by
                rw [List.ofFn_succ]
                rfl


def fkRectBoundaryAlternatingParityList : Nat -> List Bool
  | 0 => [false]
  | blocks + 1 => false :: true :: fkRectBoundaryAlternatingParityList blocks

theorem ofFn_even_succ_eq_fkRectBoundaryAlternatingParityList
    (blocks : Nat) :
    List.ofFn (fun i : Fin (2 * blocks + 1) =>
      decide (Even (i.val + 1))) =
        fkRectBoundaryAlternatingParityList blocks := by
  induction blocks with
  | zero => rfl
  | succ blocks ih =>
      rw [show 2 * (blocks + 1) + 1 = (2 * blocks + 2) + 1 by omega]
      rw [List.ofFn_succ]
      change false :: _ = _
      rw [List.ofFn_succ]
      simp only [Fin.val_succ, Fin.val_zero]
      have heven : Even (0 + 1 + 1) := by norm_num
      simp only [heven, decide_true]
      rw [fkRectBoundaryAlternatingParityList]
      simp only [List.cons.injEq, true_and]
      rw [← ih]
      congr 1
      funext i
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      simpa [Nat.add_assoc] using
        (Nat.even_add (m := i.val + 1) (n := 2))

theorem fkRect_nonSeamParityList_eq_alternating
    (R : FKRectTorus) (blocks : Nat)
    (hheight : R.height = 2 * (blocks + 1)) :
    List.ofFn (fun i : Fin (R.height - 1) =>
      decide (Even (fkRectBoundaryNonSeamRow R i).val)) =
        fkRectBoundaryAlternatingParityList blocks := by
  rw [← ofFn_even_succ_eq_fkRectBoundaryAlternatingParityList blocks]
  have hlen : R.height - 1 = 2 * blocks + 1 := by omega
  apply List.ext_get
  · simp [hlen]
  · intro n hn1 hn2
    rw [List.get_ofFn, List.get_ofFn]
    rfl


def fkRectStripTorusRowEquiv (R : FKRectTorus) :
    Fin (R.height - 1 + 1) ≃ Fin R.height :=
  finCongr (Nat.sub_add_cancel
    (Nat.one_le_iff_ne_zero.mpr R.height_pos.ne'))



def fkRectStripCoordinateTorusEquiv (R : FKRectTorus) :
    (Fin R.width × Fin (R.height - 1 + 1)) ≃ R.Vertex :=
  Equiv.prodCongr (Equiv.refl _) (fkRectStripTorusRowEquiv R)



def fkRectStripTorusVertexEquiv (R : FKRectTorus) :
    FKRectStripVertex R.width (R.height - 1) ≃ R.Vertex :=
  (fkRectStripVertexEquiv R.width (R.height - 1)).trans
    (fkRectStripCoordinateTorusEquiv R)

@[simp] theorem fkRectStripTorusRowEquiv_val
    (R : FKRectTorus) (i : Fin (R.height - 1 + 1)) :
    (fkRectStripTorusRowEquiv R i).val = i.val := rfl

@[simp] theorem fkRectStripTorusRowEquiv_succ
    (R : FKRectTorus) (i : Fin (R.height - 1)) :
    fkRectStripTorusRowEquiv R i.succ =
      fkRectBoundaryNonSeamRow R i := rfl

@[simp] theorem fkRectStripTorusRowEquiv_zero (R : FKRectTorus) :
    fkRectStripTorusRowEquiv R (0 : Fin (R.height - 1 + 1)) =
      fkRectBoundarySeamRow R := rfl

theorem fkRect_cyclicPred_nonSeamRow
    (R : FKRectTorus) (i : Fin (R.height - 1)) :
    SixVertexArrows.cyclicPred R.height_pos
        (fkRectBoundaryNonSeamRow R i) =
      fkRectStripTorusRowEquiv R i.castSucc := by
  ext
  simp only [SixVertexArrows.cyclicPred,
    fkRectBoundaryNonSeamRow_val, Fin.val_mk,
    fkRectStripTorusRowEquiv_val, Fin.val_castSucc]
  rw [show i.val + 1 + R.height - 1 = R.height + i.val by omega,
    Nat.add_mod_left, Nat.mod_eq_of_lt]
  exact i.isLt.trans_le (Nat.sub_le _ _)

theorem fkRect_cyclicPred_seamRow (R : FKRectTorus) :
    SixVertexArrows.cyclicPred R.height_pos
        (fkRectBoundarySeamRow R) =
      fkRectStripTorusRowEquiv R (Fin.last (R.height - 1)) := by
  ext
  simp only [SixVertexArrows.cyclicPred, fkRectBoundarySeamRow,
    Fin.val_mk, zero_add, fkRectStripTorusRowEquiv_val, Fin.val_last]
  rw [Nat.mod_eq_of_lt]
  all_goals have hp := R.height_pos; omega

theorem fkRectCoordinateLayerEdge_map_eq_indexedEdge
    (R : FKRectTorus) (i : Fin (R.height - 1))
    (a : Bool × Fin R.width) :
    Sym2.map (fkRectStripCoordinateTorusEquiv R)
        (fkRectCoordinateLayerEdge R.width_pos i
          (decide (Even (fkRectBoundaryNonSeamRow R i).val)) a) =
      fkRectTorusIndexedEdge R
        (a.1, (a.2, fkRectBoundaryNonSeamRow R i)) := by
  rcases a with ⟨dir, x⟩
  cases dir
  · by_cases he : Even (fkRectBoundaryNonSeamRow R i).val
    · have he' : Even (i.val + 1) := by simpa using he
      simp [fkRectCoordinateLayerEdge,
        fkRectCoordinateLayerEdgeEndpoints,
        fkRectStripCoordinateTorusEquiv, fkRectTorusIndexedEdge, he',
        fkRect_cyclicPred_nonSeamRow, Sym2.eq_swap]
    · have he' : ¬Even (i.val + 1) := by simpa using he
      simp [fkRectCoordinateLayerEdge,
        fkRectCoordinateLayerEdgeEndpoints,
        fkRectStripCoordinateTorusEquiv, fkRectTorusIndexedEdge, he',
        fkRect_cyclicPred_nonSeamRow, Sym2.eq_swap]
  · simp [fkRectCoordinateLayerEdge,
      fkRectCoordinateLayerEdgeEndpoints,
      fkRectStripCoordinateTorusEquiv, fkRectTorusIndexedEdge,
      fkRect_cyclicPred_nonSeamRow, Sym2.eq_swap]

theorem fkRectCoordinateSeamEdge_map_eq_indexedEdge
    (R : FKRectTorus) (a : Bool × Fin R.width) :
    Sym2.map (fkRectStripCoordinateTorusEquiv R)
        (fkRectCoordinateSeamEdge (n := R.height - 1) R.width_pos a) =
      fkRectTorusIndexedEdge R
        (a.1, (a.2, fkRectBoundarySeamRow R)) := by
  rcases a with ⟨dir, x⟩
  have he : Even (fkRectBoundarySeamRow R).val := by
    simp [fkRectBoundarySeamRow]
  cases dir
  · simp [fkRectCoordinateSeamEdge,
      fkRectStripCoordinateTorusEquiv, fkRectTorusIndexedEdge,
      fkRect_cyclicPred_seamRow, he, Sym2.eq_swap]
  · simp [fkRectCoordinateSeamEdge,
      fkRectStripCoordinateTorusEquiv, fkRectTorusIndexedEdge,
      fkRect_cyclicPred_seamRow, he, Sym2.eq_swap]

theorem fkRectOpenGraph_adj_iff_coordinateSchedule
    (R : FKRectTorus) (omega : R.Configuration)
    (u v : Fin R.width × Fin (R.height - 1 + 1)) :
    (fkRectOpenGraph R omega).Adj
        (fkRectStripCoordinateTorusEquiv R u)
        (fkRectStripCoordinateTorusEquiv R v) ↔
      u ≠ v ∧
        ((∃ i : Fin (R.height - 1), ∃ a : Bool × Fin R.width,
          (fkRectConfigurationNonSeamLayerFn R omega i).2 a = true ∧
            fkRectCoordinateLayerEdge R.width_pos i
                (fkRectConfigurationNonSeamLayerFn R omega i).1 a =
              s(u, v)) ∨
        ∃ a : Bool × Fin R.width,
          fkRectConfigurationLayer R omega (fkRectBoundarySeamRow R) a =
              true ∧
            fkRectCoordinateSeamEdge (n := R.height - 1)
                R.width_pos a = s(u, v)) := by
  constructor
  · intro hadj
    have hne : u ≠ v := by
      intro huv
      subst v
      exact (fkRectOpenGraph R omega).loopless.irrefl _ hadj
    refine ⟨hne, ?_⟩
    obtain ⟨⟨dir, ⟨x, y⟩⟩, hopen, hedge⟩ := hadj
    by_cases hy : y.val = 0
    · have hy' : y = fkRectBoundarySeamRow R := Fin.ext hy
      subst y
      refine Or.inr ⟨(dir, x), hopen, ?_⟩
      apply (sym2_map_eq_map_iff_of_injective
        (fkRectStripCoordinateTorusEquiv R)
        (fkRectStripCoordinateTorusEquiv R).injective _ _).1
      rw [fkRectCoordinateSeamEdge_map_eq_indexedEdge]
      simpa only [Sym2.map_pair_eq] using hedge
    · let i : Fin (R.height - 1) :=
        ⟨y.val - 1, by
          have hylt := y.isLt
          have hp := R.height_pos
          omega⟩
      have hy' : y = fkRectBoundaryNonSeamRow R i := by
        apply Fin.ext
        simp only [fkRectBoundaryNonSeamRow_val]
        dsimp only [i]
        omega
      rw [hy'] at hopen hedge
      refine Or.inl ⟨i, (dir, x), hopen, ?_⟩
      change fkRectCoordinateLayerEdge R.width_pos i
        (decide (Even (fkRectBoundaryNonSeamRow R i).val)) (dir, x) =
          s(u, v)
      apply (sym2_map_eq_map_iff_of_injective
        (fkRectStripCoordinateTorusEquiv R)
        (fkRectStripCoordinateTorusEquiv R).injective _ _).1
      rw [fkRectCoordinateLayerEdge_map_eq_indexedEdge]
      simpa only [Sym2.map_pair_eq] using hedge
  · rintro ⟨_, hnonSeam | hseam⟩
    · obtain ⟨i, a, hopen, hcoord⟩ := hnonSeam
      refine ⟨(a.1, (a.2, fkRectBoundaryNonSeamRow R i)), hopen, ?_⟩
      change fkRectCoordinateLayerEdge R.width_pos i
        (decide (Even (fkRectBoundaryNonSeamRow R i).val)) a = s(u, v)
        at hcoord
      rw [← fkRectCoordinateLayerEdge_map_eq_indexedEdge]
      rw [hcoord, Sym2.map_pair_eq]
    · obtain ⟨a, hopen, hcoord⟩ := hseam
      refine ⟨(a.1, (a.2, fkRectBoundarySeamRow R)), hopen, ?_⟩
      rw [← fkRectCoordinateSeamEdge_map_eq_indexedEdge]
      rw [hcoord, Sym2.map_pair_eq]



def fkRectConfigurationStripSeamGraph (R : FKRectTorus)
    (omega : R.Configuration) :
    SimpleGraph (FKRectStripVertex R.width (R.height - 1)) :=
  fkRectStripSeamGraph R.width_pos (R.height - 1)
    (fkRectConfigurationNonSeamLayerFn R omega)
    (fkRectConfigurationLayer R omega (fkRectBoundarySeamRow R))



noncomputable def fkRectConfigurationStripSeamIso
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectConfigurationStripSeamGraph R omega ≃g
      fkRectOpenGraph R omega where
  toEquiv := fkRectStripTorusVertexEquiv R
  map_rel_iff' := by
    intro u v
    change (fkRectOpenGraph R omega).Adj
        (fkRectStripCoordinateTorusEquiv R
          (fkRectStripVertexEquiv R.width (R.height - 1) u))
        (fkRectStripCoordinateTorusEquiv R
          (fkRectStripVertexEquiv R.width (R.height - 1) v)) ↔
      (fkRectStripSeamGraph R.width_pos (R.height - 1)
        (fkRectConfigurationNonSeamLayerFn R omega)
        (fkRectConfigurationLayer R omega
          (fkRectBoundarySeamRow R))).Adj u v
    rw [fkRectOpenGraph_adj_iff_coordinateSchedule,
      fkRectStripSeamGraph_adj_iff_coordinateEdge]
    constructor
    · rintro ⟨hne, hschedule⟩
      exact ⟨fun h => hne (congrArg
        (fkRectStripVertexEquiv R.width (R.height - 1)) h),
        hschedule⟩
    · rintro ⟨hne, hschedule⟩
      exact ⟨fun h => hne
        ((fkRectStripVertexEquiv R.width (R.height - 1)).injective h),
        hschedule⟩



theorem fkRectConfigurationStripSeamGraph_component_count
    (R : FKRectTorus) (omega : R.Configuration) :
    Fintype.card
        (fkRectConfigurationStripSeamGraph R omega).ConnectedComponent =
      fkRectBoundaryTransferClusterCount R omega := by
  have h := fkRectStripSeamGraph_component_count R.width_pos
    (R.height - 1) (fkRectConfigurationNonSeamLayerFn R omega)
    (fkRectConfigurationLayer R omega (fkRectBoundarySeamRow R))
  rw [Nat.card_eq_fintype_card] at h
  rw [fkRectStripClosedCount_eq_runClosedCount,
    fkRectStripState_eq_runState] at h
  simpa [fkRectConfigurationStripSeamGraph,
    fkRectBoundaryTransferClusterCount,
    fkRectConfigurationFinalBoundaryState] using h

theorem fkRectConfigurationStripSeamGraph_component_count_eq_numClusters
    (R : FKRectTorus) (omega : R.Configuration) :
    Fintype.card
        (fkRectConfigurationStripSeamGraph R omega).ConnectedComponent =
      fkRectNumClusters R omega := by
  unfold fkRectNumClusters
  exact Fintype.card_congr
    (fkRectConfigurationStripSeamIso R omega).connectedComponentEquiv

theorem fkRectBoundaryTransferClusterCount_eq_numClusters
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectBoundaryTransferClusterCount R omega =
      fkRectNumClusters R omega := by
  rw [← fkRectConfigurationStripSeamGraph_component_count R omega]
  exact fkRectConfigurationStripSeamGraph_component_count_eq_numClusters R omega

theorem fkRectBoundaryTransferCoefficient_eq_criticalReducedWeight
    (R : FKRectTorus) (q : Real) (omega : R.Configuration) :
    fkRectBoundaryTransferCoefficient R q omega =
      fkRectCriticalReducedWeight R q omega := by
  rw [fkRectBoundaryTransferCoefficient_eq,
    fkRectBoundaryTransferClusterCount_eq_numClusters]
  rfl

theorem fkRectBoundaryTransferClusterCount_eq_numClusters_of_geometry
    (R : FKRectTorus) (omega : R.Configuration)
    (hgeometry : Fintype.card
        (fkRectConfigurationStripSeamGraph R omega).ConnectedComponent =
      fkRectNumClusters R omega) :
    fkRectBoundaryTransferClusterCount R omega =
      fkRectNumClusters R omega := by
  rw [← fkRectConfigurationStripSeamGraph_component_count R omega]
  exact hgeometry

theorem fkRectBoundaryTransferCoefficient_eq_criticalReducedWeight_of_geometry
    (R : FKRectTorus) (q : Real) (omega : R.Configuration)
    (hgeometry : Fintype.card
        (fkRectConfigurationStripSeamGraph R omega).ConnectedComponent =
      fkRectNumClusters R omega) :
    fkRectBoundaryTransferCoefficient R q omega =
      fkRectCriticalReducedWeight R q omega := by
  rw [fkRectBoundaryTransferCoefficient_eq,
    fkRectBoundaryTransferClusterCount_eq_numClusters_of_geometry
      R omega hgeometry]
  rfl

theorem fkRectBoundaryLayerWeight_pos {W : Nat} (hW : 0 < W)
    {q : Real} (hq : 0 < q) (evenRow : Bool)
    (state : FKRectBoundaryState W) (eta : Bool × Fin W -> Bool) :
    0 < fkRectBoundaryLayerWeight hW q evenRow state eta := by
  unfold fkRectBoundaryLayerWeight
  exact mul_pos (pow_pos (Real.sqrt_pos.2 hq) _) (pow_pos hq _)

theorem fkRectBoundaryLayerTransfer_nonneg {W : Nat} (hW : 0 < W)
    {q : Real} (hq : 0 < q) (evenRow : Bool)
    (source target : FKRectBoundaryState W) :
    0 <= fkRectBoundaryLayerTransfer hW q evenRow source target := by
  classical
  unfold fkRectBoundaryLayerTransfer
  exact Finset.sum_nonneg fun eta _ => by
    split_ifs
    · exact (fkRectBoundaryLayerWeight_pos hW hq evenRow source eta).le
    · exact le_rfl




theorem fkRectBoundaryLayerTransfer_target_isConnectivity_of_pos
    {W : Nat} (hW : 0 < W) {q : Real} (hq : 0 < q)
    (evenRow : Bool) (source target : FKRectBoundaryState W)
    (hpos : 0 < fkRectBoundaryLayerTransfer hW q evenRow source target) :
    target.IsConnectivity := by
  classical
  unfold fkRectBoundaryLayerTransfer at hpos
  rw [Finset.sum_pos_iff_of_nonneg] at hpos
  · obtain ⟨eta, heta, hterm⟩ := hpos
    split at hterm <;> simp_all
    subst target
    exact fkRectBoundaryLayerOutput_isConnectivity hW evenRow source eta
  · intro eta heta
    split_ifs
    · exact (fkRectBoundaryLayerWeight_pos hW hq evenRow source eta).le
    · exact le_rfl

theorem fkRectBoundaryTwoLayerTransfer_nonneg {W : Nat} (hW : 0 < W)
    {q : Real} (hq : 0 < q) (source target : FKRectBoundaryState W) :
    0 ≤ fkRectBoundaryTwoLayerTransfer hW q source target := by
  unfold fkRectBoundaryTwoLayerTransfer
  rw [Matrix.mul_apply]
  exact Finset.sum_nonneg fun middle _ => mul_nonneg
    (fkRectBoundaryLayerTransfer_nonneg hW hq false source middle)
    (fkRectBoundaryLayerTransfer_nonneg hW hq true middle target)



theorem fkRectBoundaryTwoLayerTransfer_target_isConnectivity_of_pos
    {W : Nat} (hW : 0 < W) {q : Real} (hq : 0 < q)
    (source target : FKRectBoundaryState W)
    (hpos : 0 < fkRectBoundaryTwoLayerTransfer hW q source target) :
    target.IsConnectivity := by
  classical
  unfold fkRectBoundaryTwoLayerTransfer at hpos
  rw [Matrix.mul_apply, Finset.sum_pos_iff_of_nonneg] at hpos
  · obtain ⟨middle, hmiddle, hproduct⟩ := hpos
    have hright : 0 < fkRectBoundaryLayerTransfer hW q true middle target := by
      have hleft := fkRectBoundaryLayerTransfer_nonneg hW hq false source middle
      have hright := fkRectBoundaryLayerTransfer_nonneg hW hq true middle target
      nlinarith
    exact fkRectBoundaryLayerTransfer_target_isConnectivity_of_pos
      hW hq true middle target hright
  · intro middle hmiddle
    exact mul_nonneg
      (fkRectBoundaryLayerTransfer_nonneg hW hq false source middle)
      (fkRectBoundaryLayerTransfer_nonneg hW hq true middle target)



def fkRectBoundaryConnectivityLayerTransfer {W : Nat} (hW : 0 < W)
    (q : Real) (evenRow : Bool) :
    Matrix (FKRectBoundaryConnectivityState W)
      (FKRectBoundaryConnectivityState W) Real :=
  fun source target =>
    ∑ eta : Bool × Fin W -> Bool,
      if fkRectBoundaryConnectivityLayerOutput hW evenRow source eta = target then
        fkRectBoundaryLayerWeight hW q evenRow source.1 eta
      else 0

theorem fkRectBoundaryConnectivityLayerTransfer_nonneg
    {W : Nat} (hW : 0 < W) {q : Real} (hq : 0 < q)
    (evenRow : Bool) (source target : FKRectBoundaryConnectivityState W) :
    0 <= fkRectBoundaryConnectivityLayerTransfer hW q evenRow source target := by
  unfold fkRectBoundaryConnectivityLayerTransfer
  exact Finset.sum_nonneg fun eta _ => by
    split_ifs
    · exact (fkRectBoundaryLayerWeight_pos hW hq evenRow source.1 eta).le
    · exact le_rfl


theorem fkRectBoundaryConnectivityLayerTransfer_diag_pos
    {W : Nat} (hW : 0 < W) {q : Real} (hq : 0 < q)
    (evenRow : Bool) (state : FKRectBoundaryConnectivityState W) :
    0 < fkRectBoundaryConnectivityLayerTransfer hW q evenRow state state := by
  let vertical : Bool × Fin W -> Bool := fkRectBoundaryVerticalLayer
  have houtput : fkRectBoundaryConnectivityLayerOutput hW evenRow state vertical =
      state := by
    apply Subtype.ext
    exact fkRectBoundaryLayerOutput_vertical hW evenRow state.1 state.2
  have hterm : 0 <
      (if fkRectBoundaryConnectivityLayerOutput hW evenRow state vertical = state
        then fkRectBoundaryLayerWeight hW q evenRow state.1 vertical else 0) := by
    rw [if_pos houtput]
    exact fkRectBoundaryLayerWeight_pos hW hq evenRow state.1 vertical
  apply lt_of_lt_of_le hterm
  unfold fkRectBoundaryConnectivityLayerTransfer
  have hle := Finset.single_le_sum
    (s := Finset.univ)
    (f := fun eta : Bool × Fin W -> Bool =>
      if fkRectBoundaryConnectivityLayerOutput hW evenRow state eta = state then
        fkRectBoundaryLayerWeight hW q evenRow state.1 eta else 0)
    (fun eta _ => by
      dsimp only
      split_ifs
      · exact (fkRectBoundaryLayerWeight_pos hW hq evenRow state.1 eta).le
      · exact le_rfl)
    (Finset.mem_univ vertical)
  simpa using hle


def fkRectBoundaryConnectivityTwoLayerTransfer {W : Nat} (hW : 0 < W)
    (q : Real) :
    Matrix (FKRectBoundaryConnectivityState W)
      (FKRectBoundaryConnectivityState W) Real :=
  fkRectBoundaryConnectivityLayerTransfer hW q false *
    fkRectBoundaryConnectivityLayerTransfer hW q true

theorem fkRectBoundaryConnectivityTwoLayerTransfer_diag_pos
    {W : Nat} (hW : 0 < W) {q : Real} (hq : 0 < q)
    (state : FKRectBoundaryConnectivityState W) :
    0 < fkRectBoundaryConnectivityTwoLayerTransfer hW q state state := by
  unfold fkRectBoundaryConnectivityTwoLayerTransfer
  rw [Matrix.mul_apply]
  have hterm := mul_pos
    (fkRectBoundaryConnectivityLayerTransfer_diag_pos hW hq false state)
    (fkRectBoundaryConnectivityLayerTransfer_diag_pos hW hq true state)
  apply lt_of_lt_of_le hterm
  apply Finset.single_le_sum (fun middle _ => mul_nonneg
    (fkRectBoundaryConnectivityLayerTransfer_nonneg hW hq false state middle)
    (fkRectBoundaryConnectivityLayerTransfer_nonneg hW hq true middle state))
    (Finset.mem_univ state)



theorem fkRectBoundaryLayerTransfer_diag_pos_of_isConnectivity
    {W : Nat} (hW : 0 < W) {q : Real} (hq : 0 < q)
    (evenRow : Bool) (state : FKRectBoundaryState W)
    (hstate : state.IsConnectivity) :
    0 < fkRectBoundaryLayerTransfer hW q evenRow state state := by
  let vertical : Bool × Fin W -> Bool := fkRectBoundaryVerticalLayer
  have houtput : fkRectBoundaryLayerOutput hW evenRow state vertical = state :=
    fkRectBoundaryLayerOutput_vertical hW evenRow state hstate
  have hterm : 0 <
      (if fkRectBoundaryLayerOutput hW evenRow state vertical = state then
        fkRectBoundaryLayerWeight hW q evenRow state vertical else 0) := by
    rw [if_pos houtput]
    exact fkRectBoundaryLayerWeight_pos hW hq evenRow state vertical
  apply lt_of_lt_of_le hterm
  unfold fkRectBoundaryLayerTransfer
  exact Finset.single_le_sum
    (s := Finset.univ)
    (f := fun eta : Bool × Fin W -> Bool =>
      if fkRectBoundaryLayerOutput hW evenRow state eta = state then
        fkRectBoundaryLayerWeight hW q evenRow state eta else 0)
    (fun eta _ => by
      dsimp only
      split_ifs
      · exact (fkRectBoundaryLayerWeight_pos hW hq evenRow state eta).le
      · exact le_rfl)
    (Finset.mem_univ vertical)

theorem fkRectBoundaryTwoLayerTransfer_diag_pos_of_isConnectivity
    {W : Nat} (hW : 0 < W) {q : Real} (hq : 0 < q)
    (state : FKRectBoundaryState W) (hstate : state.IsConnectivity) :
    0 < fkRectBoundaryTwoLayerTransfer hW q state state := by
  unfold fkRectBoundaryTwoLayerTransfer
  rw [Matrix.mul_apply]
  have hterm := mul_pos
    (fkRectBoundaryLayerTransfer_diag_pos_of_isConnectivity
      hW hq false state hstate)
    (fkRectBoundaryLayerTransfer_diag_pos_of_isConnectivity
      hW hq true state hstate)
  apply lt_of_lt_of_le hterm
  exact Finset.single_le_sum
    (fun middle _ => mul_nonneg
      (fkRectBoundaryLayerTransfer_nonneg hW hq false state middle)
      (fkRectBoundaryLayerTransfer_nonneg hW hq true middle state))
    (Finset.mem_univ state)




theorem fkRectBoundaryTwoLayerTransfer_reachable_isConnectivity
    {W : Nat} (hW : 0 < W) {q : Real} (hq : 0 < q)
    (state : FKRectBoundaryState W)
    (hreach : MatrixPositiveReachable
      (fkRectBoundaryTwoLayerTransfer hW q)
      (fkRectBoundaryInitialState W) state) :
    state.IsConnectivity := by
  classical
  obtain ⟨n, hn⟩ := hreach
  cases n with
  | zero =>
      have heq : fkRectBoundaryInitialState W = state := by
        by_contra hne
        simp [hne] at hn
      subst state
      exact fkRectBoundaryInitialState_isConnectivity W
  | succ n =>
      rw [pow_succ, Matrix.mul_apply, Finset.sum_pos_iff_of_nonneg] at hn
      · obtain ⟨middle, hmiddle, hproduct⟩ := hn
        have htransition :
            0 < fkRectBoundaryTwoLayerTransfer hW q middle state := by
          have hleft := Matrix.pow_apply_nonneg
            (fkRectBoundaryTwoLayerTransfer_nonneg hW hq) n
            (fkRectBoundaryInitialState W) middle
          have hright := fkRectBoundaryTwoLayerTransfer_nonneg
            hW hq middle state
          nlinarith
        exact fkRectBoundaryTwoLayerTransfer_target_isConnectivity_of_pos
          hW hq middle state htransition
      · intro middle hmiddle
        exact mul_nonneg
          (Matrix.pow_apply_nonneg
            (fkRectBoundaryTwoLayerTransfer_nonneg hW hq) n
            (fkRectBoundaryInitialState W) middle)
          (fkRectBoundaryTwoLayerTransfer_nonneg hW hq middle state)



theorem fkRectBoundaryLayerTransfer_mulVec {W : Nat} (hW : 0 < W)
    (q : Real) (evenRow : Bool) (f : FKRectBoundaryState W -> Real)
    (source : FKRectBoundaryState W) :
    (fkRectBoundaryLayerTransfer hW q evenRow *ᵥ f) source =
      ∑ eta : Bool × Fin W -> Bool,
        fkRectBoundaryLayerWeight hW q evenRow source eta *
          f (fkRectBoundaryLayerOutput hW evenRow source eta) := by
  classical
  rw [Matrix.mulVec, dotProduct]
  unfold fkRectBoundaryLayerTransfer
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro eta heta
  simp



theorem fkRectBoundaryTwoLayerTransfer_mulVec {W : Nat} (hW : 0 < W)
    (q : Real) (f : FKRectBoundaryState W -> Real)
    (source : FKRectBoundaryState W) :
    (fkRectBoundaryTwoLayerTransfer hW q *ᵥ f) source =
      ∑ oddLayer : Bool × Fin W -> Bool,
        fkRectBoundaryLayerWeight hW q false source oddLayer *
          ∑ evenLayer : Bool × Fin W -> Bool,
            fkRectBoundaryLayerWeight hW q true
                (fkRectBoundaryLayerOutput hW false source oddLayer)
                evenLayer *
              f (fkRectBoundaryLayerOutput hW true
                (fkRectBoundaryLayerOutput hW false source oddLayer)
                evenLayer) := by
  rw [fkRectBoundaryTwoLayerTransfer, ← Matrix.mulVec_mulVec,
    fkRectBoundaryLayerTransfer_mulVec]
  apply Finset.sum_congr rfl
  intro oddLayer hodd
  rw [fkRectBoundaryLayerTransfer_mulVec]

theorem fkRectBoundarySeamFunctional_pos {W : Nat} (hW : 0 < W)
    {q : Real} (hq : 0 < q) (state : FKRectBoundaryState W) :
    0 < fkRectBoundarySeamFunctional hW q state := by
  classical
  unfold fkRectBoundarySeamFunctional fkRectBoundarySeamWeight
  exact Finset.sum_pos
    (fun eta _ => mul_pos (pow_pos (Real.sqrt_pos.2 hq) _)
      (pow_pos hq _))
    Finset.univ_nonempty



theorem fkRectBoundaryFinalFunctional_pos {W : Nat} (hW : 0 < W)
    {q : Real} (hq : 0 < q) (state : FKRectBoundaryState W) :
    0 < (fkRectBoundaryLayerTransfer hW q false *ᵥ
      fkRectBoundarySeamFunctional hW q) state := by
  rw [fkRectBoundaryLayerTransfer_mulVec]
  exact Finset.sum_pos
    (fun eta _ => mul_pos
      (fkRectBoundaryLayerWeight_pos hW hq false state eta)
      (fkRectBoundarySeamFunctional_pos hW hq
        (fkRectBoundaryLayerOutput hW false state eta)))
    Finset.univ_nonempty




def fkRectBoundaryTransferReducedZ {W : Nat} (hW : 0 < W)
    (q : Real) (blocks : Nat) : Real :=
  (((fkRectBoundaryTwoLayerTransfer hW q) ^ blocks *
      fkRectBoundaryLayerTransfer hW q false) *ᵥ
      fkRectBoundarySeamFunctional hW q)
    (fkRectBoundaryInitialState W)





theorem exists_fkRectBoundaryTransferReducedZ_log_div_tendsto
    {W : Nat} (hW : 0 < W) {q : Real} (hq : 0 < q) :
    ∃ rate : Real, Tendsto (fun blocks : Nat =>
      Real.log (fkRectBoundaryTransferReducedZ hW q blocks) /
        (blocks : Real)) atTop (nhds rate) := by
  let A := fkRectBoundaryTwoLayerTransfer hW q
  let final := fkRectBoundaryLayerTransfer hW q false *ᵥ
    fkRectBoundarySeamFunctional hW q
  have hA : ∀ source target, 0 ≤ A source target :=
    fkRectBoundaryTwoLayerTransfer_nonneg hW hq
  have hdiag : ∀ state,
      MatrixPositiveReachable A (fkRectBoundaryInitialState W) state →
        0 < A state state := by
    intro state hreach
    exact fkRectBoundaryTwoLayerTransfer_diag_pos_of_isConnectivity hW hq
      state (fkRectBoundaryTwoLayerTransfer_reachable_isConnectivity
        hW hq state hreach)
  have hfinal : ∀ state, 0 < final state :=
    fkRectBoundaryFinalFunctional_pos hW hq
  obtain ⟨rate, hrate⟩ :=
    exists_matrixCoefficient_log_div_tendsto_of_reachable_diag
      A hA (fkRectBoundaryInitialState W) hdiag final hfinal
  refine ⟨rate, ?_⟩
  simpa [A, final, fkRectBoundaryTransferReducedZ,
    Matrix.mulVec_mulVec] using hrate



def fkRectBoundaryAlternatingCoefficientSum {W : Nat} (hW : 0 < W)
    (q : Real) (state : FKRectBoundaryState W) : Nat -> Real
  | 0 =>
      ∑ oddLayer : Bool × Fin W -> Bool,
        fkRectBoundaryLayerWeight hW q false state oddLayer *
          fkRectBoundarySeamFunctional hW q
            (fkRectBoundaryLayerOutput hW false state oddLayer)
  | blocks + 1 =>
      ∑ oddLayer : Bool × Fin W -> Bool,
        fkRectBoundaryLayerWeight hW q false state oddLayer *
          ∑ evenLayer : Bool × Fin W -> Bool,
            fkRectBoundaryLayerWeight hW q true
                (fkRectBoundaryLayerOutput hW false state oddLayer)
                evenLayer *
              fkRectBoundaryAlternatingCoefficientSum hW q
                (fkRectBoundaryLayerOutput hW true
                (fkRectBoundaryLayerOutput hW false state oddLayer)
                  evenLayer) blocks

theorem fkRectBoundaryListCoefficientSum_alternating
    {W : Nat} (hW : 0 < W) (q : Real)
    (state : FKRectBoundaryState W) (blocks : Nat) :
    fkRectBoundaryListCoefficientSum hW q state
        (fkRectBoundaryAlternatingParityList blocks) =
      fkRectBoundaryAlternatingCoefficientSum hW q state blocks := by
  induction blocks generalizing state with
  | zero => rfl
  | succ blocks ih =>
      simp only [fkRectBoundaryAlternatingParityList,
        fkRectBoundaryListCoefficientSum,
        fkRectBoundaryAlternatingCoefficientSum]
      apply Finset.sum_congr rfl
      intro oddLayer hodd
      apply congrArg (fun x =>
        fkRectBoundaryLayerWeight hW q false state oddLayer * x)
      apply Finset.sum_congr rfl
      intro evenLayer heven
      rw [ih]



theorem fkRectBoundaryAlternatingCoefficientSum_eq_matrix
    {W : Nat} (hW : 0 < W) (q : Real)
    (state : FKRectBoundaryState W) (blocks : Nat) :
    fkRectBoundaryAlternatingCoefficientSum hW q state blocks =
      ((((fkRectBoundaryTwoLayerTransfer hW q) ^ blocks *
          fkRectBoundaryLayerTransfer hW q false) *ᵥ
          fkRectBoundarySeamFunctional hW q) state) := by
  induction blocks generalizing state with
  | zero =>
      simp only [fkRectBoundaryAlternatingCoefficientSum, pow_zero, one_mul]
      symm
      exact fkRectBoundaryLayerTransfer_mulVec hW q false _ _
  | succ blocks ih =>
      rw [fkRectBoundaryAlternatingCoefficientSum]
      rw [pow_succ']
      rw [Matrix.mul_assoc]
      rw [← Matrix.mulVec_mulVec]
      rw [fkRectBoundaryTwoLayerTransfer_mulVec]
      apply Finset.sum_congr rfl
      intro oddLayer hodd
      apply congrArg (fun x =>
        fkRectBoundaryLayerWeight hW q false state oddLayer * x)
      apply Finset.sum_congr rfl
      intro evenLayer heven
      rw [ih]


theorem fkRectBoundaryTransferReducedZ_eq_coefficientSum
    {W : Nat} (hW : 0 < W) (q : Real) (blocks : Nat) :
    fkRectBoundaryTransferReducedZ hW q blocks =
      fkRectBoundaryAlternatingCoefficientSum hW q
        (fkRectBoundaryInitialState W) blocks := by
  symm
  exact fkRectBoundaryAlternatingCoefficientSum_eq_matrix
    hW q (fkRectBoundaryInitialState W) blocks



theorem fkRectCriticalReducedZ_eq_boundaryTransferReducedZ
    (R : FKRectTorus) (q : Real) (blocks : Nat)
    (hheight : R.height = 2 * (blocks + 1)) :
    fkRectCriticalReducedZ R q =
      fkRectBoundaryTransferReducedZ R.width_pos q blocks := by
  unfold fkRectCriticalReducedZ
  calc
    (∑ omega : R.Configuration,
        fkRectCriticalReducedWeight R q omega) =
        ∑ omega : R.Configuration,
          fkRectBoundaryTransferCoefficient R q omega := by
            apply Finset.sum_congr rfl
            intro omega homega
            exact (fkRectBoundaryTransferCoefficient_eq_criticalReducedWeight
              R q omega).symm
    _ = ∑ layers : Fin (R.height - 1) ->
          Bool × Fin R.width -> Bool,
        fkRectBoundaryRunWeight R.width_pos q
            (fkRectBoundaryInitialState R.width)
            (List.ofFn fun i : Fin (R.height - 1) =>
              (decide (Even (fkRectBoundaryNonSeamRow R i).val),
                layers i)) *
          fkRectBoundarySeamFunctional R.width_pos q
            (fkRectBoundaryRunState R.width_pos
              (fkRectBoundaryInitialState R.width)
              (List.ofFn fun i : Fin (R.height - 1) =>
                (decide (Even (fkRectBoundaryNonSeamRow R i).val),
                  layers i))) :=
            sum_fkRectBoundaryTransferCoefficient_eq_layerSum R q
    _ = fkRectBoundaryListCoefficientSum R.width_pos q
          (fkRectBoundaryInitialState R.width)
          (List.ofFn fun i : Fin (R.height - 1) =>
            decide (Even (fkRectBoundaryNonSeamRow R i).val)) :=
            fkRectBoundaryFiniteLayerSum_eq_listCoefficientSum
              R.width_pos q (fkRectBoundaryInitialState R.width)
              (R.height - 1)
              (fun i => decide
                (Even (fkRectBoundaryNonSeamRow R i).val))
    _ = fkRectBoundaryAlternatingCoefficientSum R.width_pos q
          (fkRectBoundaryInitialState R.width) blocks := by
            rw [fkRect_nonSeamParityList_eq_alternating R blocks hheight,
              fkRectBoundaryListCoefficientSum_alternating]
    _ = fkRectBoundaryTransferReducedZ R.width_pos q blocks := by
            rw [fkRectBoundaryTransferReducedZ_eq_coefficientSum]

@[simp] theorem fkRectBoundaryTransferReducedZ_zero {W : Nat} (hW : 0 < W)
    (q : Real) :
    fkRectBoundaryTransferReducedZ hW q 0 =
      ∑ oddLayer : Bool × Fin W -> Bool,
        fkRectBoundaryLayerWeight hW q false
            (fkRectBoundaryInitialState W) oddLayer *
          fkRectBoundarySeamFunctional hW q
            (fkRectBoundaryLayerOutput hW false
              (fkRectBoundaryInitialState W) oddLayer) := by
  simp only [fkRectBoundaryTransferReducedZ, pow_zero, one_mul]
  exact fkRectBoundaryLayerTransfer_mulVec hW q false _ _

end

end StatMech.FrontierD
