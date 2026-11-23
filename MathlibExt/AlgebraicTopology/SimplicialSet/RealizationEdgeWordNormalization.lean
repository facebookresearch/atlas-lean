/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RealizationEdgeWord
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RealizationSignedGrid

/-!
# Signed normalization of realization edge words

This file normalizes a realization edge word to a finite dependent chain of
signed simplicial edges. The chain retains its literal vertices, represented
fundamental-groupoid morphism, and concatenated realized path. Formal inverse
reverses the order and traversal of the signed edges, and composition appends
chains.

Two words with the same endpoints have a common-length normalization obtained
only by appending signed identities at the common target. Both represented
morphisms and endpoint-fixed path-homotopy classes are preserved. The resulting
chains expose exactly the bottom and top row data expected by
`RelativeGridCertificate`, with literal constant side data.

This file does not construct a grid, target triangle, simplicial
approximation, or certificate witness, and it makes no fullness, faithfulness,
weak-equivalence, or model-category claim.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory
open scoped Simplicial

namespace SSet.RealizationEdgeWord

variable {X : SSet.{u}}

/-- A canonical literal vertex representing an arbitrary object of the
simplicial fundamental groupoid. -/
abbrev vertexRep (a : SSet.FundamentalGroupoid X) : X _⦋0⦌ :=
  a.pt

/-- The canonical representative has the original fundamental-groupoid
object. -/
abbrev mkVertexRepEq (a : SSet.FundamentalGroupoid X) :
    SSet.FundamentalGroupoid.mk (vertexRep a) = a :=
  rfl

/-- The realized canonical representative is the point underlying the image
of the original fundamental-groupoid object. -/
abbrev realizationObjEq (a : SSet.FundamentalGroupoid X) :
    ((SSet.realizationFundamentalGroupoidFunctor X).obj a).as =
      SSet.realizedVertex (vertexRep a) :=
  rfl

@[simp]
theorem vertexRep_mk (x : X _⦋0⦌) :
    vertexRep (SSet.FundamentalGroupoid.mk x) = x :=
  rfl

@[simp]
theorem mkVertexRepEq_mk (x : X _⦋0⦌) :
    mkVertexRepEq (SSet.FundamentalGroupoid.mk x) = rfl :=
  rfl

@[simp]
theorem realizationObjEq_mk (x : X _⦋0⦌) :
    realizationObjEq (SSet.FundamentalGroupoid.mk x) = rfl :=
  rfl

/-- A finite chain of signed edges with literal source, target, intermediate
vertices, and length. -/
inductive SignedChain (X : SSet.{u}) :
    ℕ → X _⦋0⦌ → X _⦋0⦌ → Type u where
| nil (x : X _⦋0⦌) : SignedChain X 0 x x
| snoc {n : ℕ} {x y z : X _⦋0⦌}
    (c : SignedChain X n x y) (e : SSet.SignedEdge X y z) :
    SignedChain X (n + 1) x z

namespace SignedChain

variable {n m : ℕ} {x y z : X _⦋0⦌}

private noncomputable def signedEdgeToWord {x y : X _⦋0⦌}
    (e : SSet.SignedEdge X x y) :
    SSet.RealizationEdgeWord X (SSet.FundamentalGroupoid.mk x)
      (SSet.FundamentalGroupoid.mk y) := by
  rcases e.data with e | e
  · exact SSet.RealizationEdgeWord.edge _ _ e
  · rcases e with e | h
    · exact (SSet.RealizationEdgeWord.edge _ _ e).inverse
    · rcases h with ⟨h⟩
      subst y
      exact SSet.RealizationEdgeWord.identity _

private theorem signedEdgeToWord_toHom {x y : X _⦋0⦌}
    (e : SSet.SignedEdge X x y) : (signedEdgeToWord e).toHom = e.toHom := by
  rcases e with ⟨e | e⟩
  · rfl
  · rcases e with e | h
    · exact (SSet.SignedEdge.toHom_reverse e).symm
    · cases h.down
      rfl

/-- The realized path of one signed edge. A reverse traversal reverses an
existing realized edge path; it does not require an opposite simplicial edge. -/
noncomputable def signedEdgeRealizedPath {x y : X _⦋0⦌}
    (e : SSet.SignedEdge X x y) :
    _root_.Path (SSet.realizedVertex x) (SSet.realizedVertex y) := by
  rcases e.data with e | e
  · exact TopCat.pathEquiv (SSet.realizedEdgePath e)
  · rcases e with e | h
    · exact (TopCat.pathEquiv (SSet.realizedEdgePath e)).symm
    · rcases h with ⟨h⟩
      subst y
      exact _root_.Path.refl _

private theorem signedEdgeToWord_realizedPath {x y : X _⦋0⦌}
    (e : SSet.SignedEdge X x y) :
    (signedEdgeToWord e).realizedPath = signedEdgeRealizedPath e := by
  rcases e with ⟨e | e⟩
  · rfl
  · rcases e with e | h
    · rfl
    · cases h.down
      rfl

private theorem map_signedEdge_toHom_eq_mk_realizedPath
    {x y : X _⦋0⦌} (e : SSet.SignedEdge X x y) :
    (SSet.realizationFundamentalGroupoidFunctor X).map e.toHom =
      _root_.Path.Homotopic.Quotient.mk (signedEdgeRealizedPath e) := by
  rw [← signedEdgeToWord_toHom]
  rw [SSet.RealizationEdgeWord.map_toHom_eq_mk_realizedPath,
    signedEdgeToWord_realizedPath]
  rfl

/-- The fundamental-groupoid morphism represented by a signed chain. -/
def toHom {n : ℕ} {x y : X _⦋0⦌} (c : SignedChain X n x y) :
    SSet.FundamentalGroupoid.mk x ⟶ SSet.FundamentalGroupoid.mk y :=
  match c with
  | .nil _ => 𝟙 _
  | .snoc c e => c.toHom ≫ e.toHom

/-- The endpoint-fixed realized path represented by a signed chain. -/
noncomputable def realizedPath {n : ℕ} {x y : X _⦋0⦌}
    (c : SignedChain X n x y) :
    _root_.Path (SSet.realizedVertex x) (SSet.realizedVertex y) :=
  match c with
  | .nil x => _root_.Path.refl (SSet.realizedVertex x)
  | .snoc c e => c.realizedPath.trans (signedEdgeRealizedPath e)

@[simp]
theorem toHom_nil (x : X _⦋0⦌) : (SignedChain.nil x).toHom = 𝟙 _ :=
  rfl

@[simp]
theorem toHom_snoc (c : SignedChain X n x y) (e : SSet.SignedEdge X y z) :
    (SignedChain.snoc c e).toHom = c.toHom ≫ e.toHom :=
  rfl

@[simp]
theorem realizedPath_nil (x : X _⦋0⦌) :
    (SignedChain.nil x).realizedPath =
      _root_.Path.refl (SSet.realizedVertex x) :=
  rfl

@[simp]
theorem realizedPath_snoc (c : SignedChain X n x y)
    (e : SSet.SignedEdge X y z) :
    (SignedChain.snoc c e).realizedPath =
      c.realizedPath.trans (signedEdgeRealizedPath e) :=
  rfl

/-- Append two dependent signed chains. -/
def append {n : ℕ} {x y : X _⦋0⦌} (c : SignedChain X n x y)
    {m : ℕ} {z : X _⦋0⦌} (d : SignedChain X m y z) :
    SignedChain X (n + m) x z :=
  match d with
  | .nil _ => c
  | .snoc d e => .snoc (c.append d) e

/-- Prepend one signed edge to a dependent signed chain. -/
def cons {x y : X _⦋0⦌} (e : SSet.SignedEdge X x y)
    {n : ℕ} {z : X _⦋0⦌} (c : SignedChain X n y z) :
    SignedChain X (n + 1) x z :=
  match c with
  | .nil _ => .snoc (.nil x) e
  | .snoc c f => .snoc (cons e c) f

/-- Reverse order and signed traversal in a dependent chain. -/
def reverse {n : ℕ} {x y : X _⦋0⦌} (c : SignedChain X n x y) :
    SignedChain X n y x :=
  match c with
  | .nil _ => .nil _
  | .snoc c e => cons e.reverseTraversal c.reverse

@[simp]
theorem toHom_append (c : SignedChain X n x y) (d : SignedChain X m y z) :
    (c.append d).toHom = c.toHom ≫ d.toHom := by
  induction d with
  | nil => simp [append]
  | snoc d e ih => simp [append, ih, Category.assoc]

@[simp]
theorem toHom_cons (e : SSet.SignedEdge X x y) (c : SignedChain X n y z) :
    (c.cons e).toHom = e.toHom ≫ c.toHom := by
  induction c with
  | nil => simp [cons]
  | snoc c f ih => simp [cons, ih, Category.assoc]

@[simp]
theorem toHom_reverse (c : SignedChain X n x y) :
    c.reverse.toHom = inv c.toHom := by
  induction c with
  | nil => simp [reverse]
  | snoc c e ih => simp [reverse, ih]

/-- The direct realization functor maps the chain composite to the
endpoint-fixed path-homotopy class of its realized path. -/
@[simp]
theorem map_toHom_eq_mk_realizedPath (c : SignedChain X n x y) :
    (SSet.realizationFundamentalGroupoidFunctor X).map c.toHom =
      _root_.Path.Homotopic.Quotient.mk c.realizedPath := by
  induction c with
  | nil x => simp [realizedPath, FundamentalGroupoid.id_eq_path_refl]
  | snoc c e ih =>
      simp [realizedPath, ih, map_signedEdge_toHom_eq_mk_realizedPath,
        FundamentalGroupoid.comp_eq]

/-- The chain of `n` literal signed identities at one vertex. -/
def identities (x : X _⦋0⦌) (n : ℕ) : SignedChain X n x x :=
  Nat.rec (.nil x) (fun _ c => .snoc c (SSet.SignedEdge.identity x)) n

@[simp]
theorem toHom_identities (x : X _⦋0⦌) (n : ℕ) :
    (identities x n).toHom = 𝟙 _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (SignedChain.snoc (identities x n)
        (SSet.SignedEdge.identity x)).toHom = 𝟙 _
      simp [ih]

/-- Append exactly `k` literal signed identities at a chain's target. -/
def padRight (c : SignedChain X n x y) (k : ℕ) :
    SignedChain X (n + k) x y :=
  c.append (identities y k)

@[simp]
theorem toHom_padRight (c : SignedChain X n x y) (k : ℕ) :
    (c.padRight k).toHom = c.toHom := by
  simp [padRight]

@[simp]
theorem mk_realizedPath_padRight (c : SignedChain X n x y) (k : ℕ) :
    _root_.Path.Homotopic.Quotient.mk (c.padRight k).realizedPath =
      _root_.Path.Homotopic.Quotient.mk c.realizedPath := by
  rw [← map_toHom_eq_mk_realizedPath (c.padRight k), toHom_padRight,
    map_toHom_eq_mk_realizedPath c]

/-- Cast only the length index of a signed chain. -/
def castLength {n m : ℕ} {x y : X _⦋0⦌} (h : n = m)
    (c : SignedChain X n x y) : SignedChain X m x y :=
  h ▸ c

@[simp]
theorem toHom_castLength {n m : ℕ} {x y : X _⦋0⦌}
    (h : n = m) (c : SignedChain X n x y) :
    (c.castLength h).toHom = c.toHom := by
  subst m
  rfl

@[simp]
theorem mk_realizedPath_castLength {n m : ℕ} {x y : X _⦋0⦌}
    (h : n = m) (c : SignedChain X n x y) :
    _root_.Path.Homotopic.Quotient.mk (c.castLength h).realizedPath =
      _root_.Path.Homotopic.Quotient.mk c.realizedPath := by
  subst m
  rfl

/-- Pad a signed chain to a specified greater length using only identities at
its target. -/
def padTo {n : ℕ} {x y : X _⦋0⦌} (N : ℕ) (h : n ≤ N)
    (c : SignedChain X n x y) : SignedChain X N x y :=
  (c.padRight (N - n)).castLength (Nat.add_sub_of_le h)

@[simp]
theorem toHom_padTo {n : ℕ} {x y : X _⦋0⦌}
    (N : ℕ) (h : n ≤ N) (c : SignedChain X n x y) :
    (c.padTo N h).toHom = c.toHom := by
  simp [padTo]

@[simp]
theorem mk_realizedPath_padTo {n : ℕ} {x y : X _⦋0⦌}
    (N : ℕ) (h : n ≤ N) (c : SignedChain X n x y) :
    _root_.Path.Homotopic.Quotient.mk (c.padTo N h).realizedPath =
      _root_.Path.Homotopic.Quotient.mk c.realizedPath := by
  simp [padTo]

/-- The vertex at one column of a dependent signed chain. -/
def vertexAt {n : ℕ} {x y : X _⦋0⦌} (c : SignedChain X n x y) :
    Fin (n + 1) → X _⦋0⦌ :=
  match c with
  | .nil x => fun _ => x
  | @snoc _ n _ _ z c _ => Fin.lastCases z (fun i => c.vertexAt i)

@[simp]
theorem vertexAt_last {n : ℕ} {x y : X _⦋0⦌}
    (c : SignedChain X n x y) : c.vertexAt (Fin.last n) = y := by
  cases c with
  | nil => rfl
  | snoc c e => simp only [vertexAt, Fin.lastCases_last]

@[simp]
theorem vertexAt_zero {n : ℕ} {x y : X _⦋0⦌}
    (c : SignedChain X n x y) : c.vertexAt 0 = x := by
  induction c with
  | nil => rfl
  | @snoc n x y z c e ih =>
      change Fin.lastCases z (fun i => c.vertexAt i) 0 = x
      rw [show (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc by rfl,
        Fin.lastCases_castSucc]
      exact ih

/-- Transport both literal endpoints of a signed edge. -/
def castEdge {x y x' y' : X _⦋0⦌} (e : SSet.SignedEdge X x y)
    (hx : x = x') (hy : y = y') : SSet.SignedEdge X x' y' := by
  subst x'
  subst y'
  exact e

@[simp]
theorem toHom_castEdge {x y x' y' : X _⦋0⦌}
    (e : SSet.SignedEdge X x y) (hx : x = x') (hy : y = y') :
    (castEdge e hx hy).toHom =
      eqToHom (congrArg SSet.FundamentalGroupoid.mk hx).symm ≫
        e.toHom ≫ eqToHom (congrArg SSet.FundamentalGroupoid.mk hy) := by
  subst x'
  subst y'
  simp [castEdge]

/-- The signed edge at one column of a dependent signed chain. -/
def edgeAt {n : ℕ} {x y : X _⦋0⦌} (c : SignedChain X n x y) :
    ∀ i : Fin n, SSet.SignedEdge X
      (c.vertexAt i.castSucc) (c.vertexAt i.succ) :=
  match c with
  | .nil _ => fun i => Fin.elim0 i
  | .snoc c e => fun i =>
      Fin.lastCases
        (castEdge e
          (by simp only [vertexAt, Fin.lastCases_castSucc, vertexAt_last])
          (by rw [Fin.succ_last]
              simp only [vertexAt, Fin.lastCases_last]))
        (fun j => castEdge (c.edgeAt j)
          (by simp only [vertexAt, Fin.lastCases_castSucc])
          (by rw [Fin.succ_castSucc]
              simp only [vertexAt, Fin.lastCases_castSucc])) i

@[simp]
theorem vertexAt_snoc_castSucc (c : SignedChain X n x y)
    (e : SSet.SignedEdge X y z) (i : Fin (n + 1)) :
    (SignedChain.snoc c e).vertexAt i.castSucc = c.vertexAt i := by
  simp only [vertexAt, Fin.lastCases_castSucc]

/-- The canonical `ComposableArrows` row determined by a signed chain. -/
noncomputable def toComposableArrows {n : ℕ} {x y : X _⦋0⦌}
    (c : SignedChain X n x y) :
    ComposableArrows (SSet.FundamentalGroupoid X) n :=
  ComposableArrows.mkOfObjOfMapSucc
    (fun i => SSet.FundamentalGroupoid.mk (c.vertexAt i))
    (fun i => (c.edgeAt i).toHom)

end SignedChain

end SSet.RealizationEdgeWord

namespace RealizationEdgeWordNormalizationAux

variable {C : Type*} [Category C]

private noncomputable def signedRowCompositeAux
    (n : ℕ) (obj : Fin (n + 1) → C)
    (mapSucc : ∀ i : Fin n, obj i.castSucc ⟶ obj i.succ) :
    obj 0 ⟶ obj (Fin.last n) :=
  match n with
  | 0 => 𝟙 _
  | n + 1 =>
      signedRowCompositeAux n (fun i => obj i.castSucc)
          (fun i => mapSucc i.castSucc) ≫
        mapSucc (Fin.last n) ≫
          eqToHom (congrArg obj (Fin.succ_last n))
termination_by n

private theorem signedRowCompositeAux_heq
    (n : ℕ) {obj obj' : Fin (n + 1) → C}
    {mapSucc : ∀ i : Fin n, obj i.castSucc ⟶ obj i.succ}
    {mapSucc' : ∀ i : Fin n, obj' i.castSucc ⟶ obj' i.succ}
    (hobj : ∀ i, obj i = obj' i)
    (hmap : ∀ i, mapSucc i ≍ mapSucc' i) :
    signedRowCompositeAux n obj mapSucc ≍
      signedRowCompositeAux n obj' mapSucc' := by
  have hobj' : obj = obj' := funext hobj
  subst obj'
  have hmap' : mapSucc = mapSucc' := funext fun i => eq_of_heq (hmap i)
  subst mapSucc'
  rfl

private theorem mkOfObjOfMapSucc_hom_eq_signedRowCompositeAux
    : ∀ (n : ℕ) (obj : Fin (n + 1) → C)
      (mapSucc : ∀ i : Fin n, obj i.castSucc ⟶ obj i.succ),
      (ComposableArrows.mkOfObjOfMapSucc obj mapSucc).hom =
        signedRowCompositeAux n obj mapSucc := by
  intro n
  induction n with
  | zero =>
      intro obj mapSucc
      simp only [signedRowCompositeAux]
      change (ComposableArrows.mkOfObjOfMapSucc obj mapSucc).map' 0 0 = 𝟙 _
      exact ComposableArrows.map'_self _ 0
  | succ n ih =>
      intro obj mapSucc
      let F := ComposableArrows.mkOfObjOfMapSucc obj mapSucc
      let obj' : Fin (n + 1) → C := fun i => obj i.castSucc
      let mapSucc' : ∀ i : Fin n, obj' i.castSucc ⟶ obj' i.succ :=
        fun i => mapSucc i.castSucc
      let F' := ComposableArrows.mkOfObjOfMapSucc obj' mapSucc'
      have hδ : F.δlast = F' := by
        refine ComposableArrows.ext (fun _ => rfl) ?_
        intro i hi
        apply (conj_eqToHom_iff_heq _ _ (by rfl) (by rfl)).2
        have hf := ComposableArrows.mkOfObjOfMapSucc_map_succ
          obj mapSucc i (by omega)
        have hf' := ComposableArrows.mkOfObjOfMapSucc_map_succ
          obj' mapSucc' i hi
        change F.map' i (i + 1) = _ at hf
        change F'.map' i (i + 1) = _ at hf'
        have h1 : F.δlast.map' i (i + 1) ≍ F.map' i (i + 1) := by
          rfl
        have h2 : F.map' i (i + 1) ≍ mapSucc ⟨i, by omega⟩ :=
          heq_of_eq hf
        have h3 : mapSucc ⟨i, by omega⟩ ≍ mapSucc' ⟨i, hi⟩ := by
          rfl
        have h4 : mapSucc' ⟨i, hi⟩ ≍ F'.map' i (i + 1) :=
          heq_of_eq hf'.symm
        exact h1.trans (h2.trans (h3.trans h4))
      have hp : F.map' 0 n = F'.hom := by
        have h := Functor.congr_hom hδ
          (homOfLE (show (0 : Fin (n + 1)) ≤ Fin.last n by simp))
        apply eq_of_heq
        exact (conj_eqToHom_iff_heq _ _
          (Functor.congr_obj hδ 0)
          (Functor.congr_obj hδ (Fin.last n))).1 h
      rw [show F.hom = F.map' 0 n ≫ F.map' n (n + 1) from
        F.map'_comp 0 n (n + 1), hp,
        ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ n (by omega),
        ih obj' mapSucc']
      simp only [signedRowCompositeAux, eqToHom_refl, Category.comp_id]
      dsimp only [obj', mapSucc']
      congr 1

/-- The canonical `ComposableArrows` row has the same composite as the
recursive signed-chain interpretation, with its literal endpoint casts. -/
@[simp]
theorem _root_.SSet.RealizationEdgeWord.SignedChain.rowComposite_eq_toHom
    {X : SSet.{u}} {n : ℕ} {x y : X _⦋0⦌}
    (c : SSet.RealizationEdgeWord.SignedChain X n x y) :
    c.toComposableArrows.hom =
      eqToHom (congrArg SSet.FundamentalGroupoid.mk c.vertexAt_zero) ≫
        c.toHom ≫
        eqToHom
          (congrArg SSet.FundamentalGroupoid.mk c.vertexAt_last).symm := by
  unfold SSet.RealizationEdgeWord.SignedChain.toComposableArrows
  rw [mkOfObjOfMapSucc_hom_eq_signedRowCompositeAux]
  apply (conj_eqToHom_iff_heq _ _
    (congrArg SSet.FundamentalGroupoid.mk c.vertexAt_zero)
    (congrArg SSet.FundamentalGroupoid.mk c.vertexAt_last)).2
  induction c with
  | nil x =>
      simp only [signedRowCompositeAux,
        SSet.RealizationEdgeWord.SignedChain.vertexAt,
        SSet.RealizationEdgeWord.SignedChain.toHom]
      rfl
  | snoc c e ih =>
      rename_i n' x' y' z'
      simp only [signedRowCompositeAux]
      have hp :
          signedRowCompositeAux _
              (fun i => SSet.FundamentalGroupoid.mk
                ((SSet.RealizationEdgeWord.SignedChain.snoc c e).vertexAt
                  i.castSucc))
              (fun i =>
                ((SSet.RealizationEdgeWord.SignedChain.snoc c e).edgeAt
                  i.castSucc).toHom) ≍
            signedRowCompositeAux _
              (fun i => SSet.FundamentalGroupoid.mk (c.vertexAt i))
              (fun i => (c.edgeAt i).toHom) := by
        apply signedRowCompositeAux_heq
        · intro i
          exact congrArg SSet.FundamentalGroupoid.mk
            (SSet.RealizationEdgeWord.SignedChain.vertexAt_snoc_castSucc
              c e i)
        · intro i
          simp only [SSet.RealizationEdgeWord.SignedChain.edgeAt,
            Fin.lastCases_castSucc,
            SSet.RealizationEdgeWord.SignedChain.toHom_castEdge]
          simp
      have hp' := hp.trans ih
      have hl :
          ((SSet.RealizationEdgeWord.SignedChain.snoc c e).edgeAt
              (Fin.last _)).toHom ≍ e.toHom := by
        simp only [SSet.RealizationEdgeWord.SignedChain.edgeAt,
          Fin.lastCases_last,
          SSet.RealizationEdgeWord.SignedChain.toHom_castEdge]
        simp
      let hlastIndex := congrArg
        (fun i : Fin (n' + 2) => SSet.FundamentalGroupoid.mk
          ((SSet.RealizationEdgeWord.SignedChain.snoc c e).vertexAt i))
        (Fin.succ_last n')
      change (_ ≫ _ ≫ eqToHom _) ≍ c.toHom ≫ e.toHom
      have hlast :
          ((SSet.RealizationEdgeWord.SignedChain.snoc c e).edgeAt
              (Fin.last _)).toHom ≫ eqToHom hlastIndex ≍ e.toHom :=
        (comp_eqToHom_heq _ hlastIndex).trans hl
      exact heq_comp
        (congrArg SSet.FundamentalGroupoid.mk
          ((SSet.RealizationEdgeWord.SignedChain.vertexAt_snoc_castSucc
              c e 0).trans c.vertexAt_zero))
        (congrArg SSet.FundamentalGroupoid.mk
          ((SSet.RealizationEdgeWord.SignedChain.vertexAt_snoc_castSucc
              c e (Fin.last _)).trans c.vertexAt_last))
        (congrArg SSet.FundamentalGroupoid.mk
          (SSet.RealizationEdgeWord.SignedChain.snoc c e).vertexAt_last)
        hp' hlast

end RealizationEdgeWordNormalizationAux

namespace SSet.RealizationEdgeWord

variable {X : SSet.{u}}

/-- A signed chain between canonical literal representatives of two arbitrary
fundamental-groupoid objects. -/
abbrev Normalized (X : SSet.{u}) (a b : SSet.FundamentalGroupoid X) :=
  Σ n, SignedChain X n (vertexRep a) (vertexRep b)

/-- Reverse a normalized chain. -/
def reverseNormalized {a b : SSet.FundamentalGroupoid X}
    (c : Normalized X a b) : Normalized X b a :=
  ⟨c.1, c.2.reverse⟩

/-- Append normalized chains with a common arbitrary object. -/
def appendNormalized {a b c : SSet.FundamentalGroupoid X}
    (p : Normalized X a b) (q : Normalized X b c) : Normalized X a c :=
  ⟨p.1 + q.1, p.2.append q.2⟩

/-- Interpret a normalized chain as a morphism between its original arbitrary
fundamental-groupoid endpoints. -/
noncomputable def normalizedToHom {a b : SSet.FundamentalGroupoid X}
    (c : Normalized X a b) : a ⟶ b :=
  eqToHom (mkVertexRepEq a).symm ≫ c.2.toHom ≫ eqToHom (mkVertexRepEq b)

/-- Interpret a normalized chain as a path between the realized images of its
original arbitrary endpoints. -/
noncomputable def normalizedRealizedPath {a b : SSet.FundamentalGroupoid X}
    (c : Normalized X a b) :
    _root_.Path ((SSet.realizationFundamentalGroupoidFunctor X).obj a).as
      ((SSet.realizationFundamentalGroupoidFunctor X).obj b).as :=
  c.2.realizedPath.cast (realizationObjEq a) (realizationObjEq b)

@[simp]
theorem normalizedToHom_reverse {a b : SSet.FundamentalGroupoid X}
    (c : Normalized X a b) :
    normalizedToHom (reverseNormalized c) = inv (normalizedToHom c) := by
  simp [normalizedToHom, reverseNormalized]

@[simp]
theorem normalizedToHom_append {a b c : SSet.FundamentalGroupoid X}
    (p : Normalized X a b) (q : Normalized X b c) :
    normalizedToHom (appendNormalized p q) =
      normalizedToHom p ≫ normalizedToHom q := by
  simp [normalizedToHom, appendNormalized]

/-- The direct realization functor maps a transported normalized composite to
the quotient class of its endpoint-transported realized path. -/
@[simp]
theorem map_normalizedToHom_eq_mk_normalizedRealizedPath
    {a b : SSet.FundamentalGroupoid X} (c : Normalized X a b) :
    (SSet.realizationFundamentalGroupoidFunctor X).map (normalizedToHom c) =
      _root_.Path.Homotopic.Quotient.mk (normalizedRealizedPath c) := by
  let R := SSet.realizationFundamentalGroupoidFunctor X
  have hleft : R.map (eqToHom (mkVertexRepEq a).symm) =
      eqToHom (congrArg _root_.FundamentalGroupoid.mk
        (realizationObjEq a)) := by
    rw [eqToHom_map]
    congr 1
  have hright : R.map (eqToHom (mkVertexRepEq b)) =
      eqToHom (congrArg _root_.FundamentalGroupoid.mk
        (realizationObjEq b).symm) := by
    rw [eqToHom_map]
    congr 1
  rw [normalizedToHom, normalizedRealizedPath, Functor.map_comp,
    Functor.map_comp, hleft, hright,
    SignedChain.map_toHom_eq_mk_realizedPath,
    _root_.Path.Homotopic.Quotient.mk_cast]
  exact _root_.FundamentalGroupoid.conj_eqToHom (realizationObjEq a)
    (realizationObjEq b)

/-- Normalize an indexed realization edge word to a finite signed chain. -/
noncomputable def normalize {a b : SSet.FundamentalGroupoid X}
    (w : SSet.RealizationEdgeWord X a b) : Normalized X a b :=
  @SSet.RealizationEdgeWord.rec X (fun a b _ => Normalized X a b)
    (fun x _ e => ⟨1, .snoc (.nil x) (.forward e)⟩)
    (fun a => ⟨0, .nil (vertexRep a)⟩)
    (fun {_ _} _ c => reverseNormalized c)
    (fun {_ _ _} _ _ p q => appendNormalized p q) _ _ w

@[simp]
theorem normalize_edge (x y : X _⦋0⦌) (e : X.Edge x y) :
    normalize (SSet.RealizationEdgeWord.edge x y e) =
      ⟨1, .snoc (.nil x) (.forward e)⟩ :=
  rfl

@[simp]
theorem normalize_identity (a : SSet.FundamentalGroupoid X) :
    normalize (SSet.RealizationEdgeWord.identity a) =
      ⟨0, .nil (vertexRep a)⟩ :=
  rfl

@[simp]
theorem normalize_inverse {a b : SSet.FundamentalGroupoid X}
    (w : SSet.RealizationEdgeWord X a b) :
    normalize w.inverse = reverseNormalized (normalize w) :=
  rfl

@[simp]
theorem normalize_compose {a b c : SSet.FundamentalGroupoid X}
    (w : SSet.RealizationEdgeWord X a b)
    (w' : SSet.RealizationEdgeWord X b c) :
    normalize (w.compose w') = appendNormalized (normalize w) (normalize w') :=
  rfl

/-- Normalization preserves the represented fundamental-groupoid morphism. -/
@[simp]
theorem normalize_toHom {a b : SSet.FundamentalGroupoid X}
    (w : SSet.RealizationEdgeWord X a b) :
    normalizedToHom (normalize w) = w.toHom := by
  induction w with
  | edge x y e =>
      change eqToHom _ ≫ (𝟙 _ ≫ SSet.FundamentalGroupoid.homMk e) ≫
        eqToHom _ = SSet.FundamentalGroupoid.homMk e
      rw [eqToHom_refl, eqToHom_refl]
      simp
  | identity obj =>
      induction obj using SSet.FundamentalGroupoid.rec
      rfl
  | inverse w ih =>
      rw [normalize_inverse, normalizedToHom_reverse, ih]
      rfl
  | compose w w' ih ih' =>
      rw [normalize_compose, normalizedToHom_append, ih, ih']
      rfl

/-- Normalization preserves the endpoint-fixed path-homotopy quotient class. -/
@[simp]
theorem normalize_realizedPath_class
    {a b : SSet.FundamentalGroupoid X} (w : SSet.RealizationEdgeWord X a b) :
    _root_.Path.Homotopic.Quotient.mk
        (normalizedRealizedPath (normalize w)) =
      _root_.Path.Homotopic.Quotient.mk w.realizedPath := by
  rw [← map_normalizedToHom_eq_mk_normalizedRealizedPath, normalize_toHom,
    SSet.RealizationEdgeWord.map_toHom_eq_mk_realizedPath]

/-- Pad a normalized chain to a greater length using only identities at its
literal target representative. -/
def padNormalizedTo {a b : SSet.FundamentalGroupoid X}
    (c : Normalized X a b) (N : ℕ) (h : c.1 ≤ N) : Normalized X a b :=
  ⟨N, c.2.padTo N h⟩

@[simp]
theorem normalizedToHom_padNormalizedTo
    {a b : SSet.FundamentalGroupoid X} (c : Normalized X a b)
    (N : ℕ) (h : c.1 ≤ N) :
    normalizedToHom (padNormalizedTo c N h) = normalizedToHom c := by
  simp [padNormalizedTo, normalizedToHom]

@[simp]
theorem mk_normalizedRealizedPath_padNormalizedTo
    {a b : SSet.FundamentalGroupoid X} (c : Normalized X a b)
    (N : ℕ) (h : c.1 ≤ N) :
    _root_.Path.Homotopic.Quotient.mk
        (normalizedRealizedPath (padNormalizedTo c N h)) =
      _root_.Path.Homotopic.Quotient.mk (normalizedRealizedPath c) := by
  simp only [normalizedRealizedPath,
    _root_.Path.Homotopic.Quotient.mk_cast]
  exact congrArg
    (fun q => q.cast (realizationObjEq a) (realizationObjEq b))
    (SignedChain.mk_realizedPath_padTo N h c.2)

/-- Two same-endpoint words normalized to one common length using only
identity insertion. -/
structure CommonNormalization {a b : SSet.FundamentalGroupoid X}
    (w w' : SSet.RealizationEdgeWord X a b) where
  length : ℕ
  left : SignedChain X length (vertexRep a) (vertexRep b)
  right : SignedChain X length (vertexRep a) (vertexRep b)
  left_toHom : normalizedToHom ⟨length, left⟩ = w.toHom
  right_toHom : normalizedToHom ⟨length, right⟩ = w'.toHom
  left_path_class : _root_.Path.Homotopic.Quotient.mk
    (normalizedRealizedPath ⟨length, left⟩) =
      _root_.Path.Homotopic.Quotient.mk w.realizedPath
  right_path_class : _root_.Path.Homotopic.Quotient.mk
    (normalizedRealizedPath ⟨length, right⟩) =
      _root_.Path.Homotopic.Quotient.mk w'.realizedPath

/-- The total common-length identity-only normalization of two same-endpoint
words. -/
noncomputable def commonNormalization
    {a b : SSet.FundamentalGroupoid X}
    (w w' : SSet.RealizationEdgeWord X a b) : CommonNormalization w w' := by
  let p := normalize w
  let q := normalize w'
  let N := max p.1 q.1
  let p' := padNormalizedTo p N (le_max_left _ _)
  let q' := padNormalizedTo q N (le_max_right _ _)
  refine
    { length := N
      left := p'.2
      right := q'.2
      left_toHom := ?_
      right_toHom := ?_
      left_path_class := ?_
      right_path_class := ?_ }
  · change normalizedToHom p' = w.toHom
    rw [normalizedToHom_padNormalizedTo, normalize_toHom]
  · change normalizedToHom q' = w'.toHom
    rw [normalizedToHom_padNormalizedTo, normalize_toHom]
  · change _root_.Path.Homotopic.Quotient.mk
      (normalizedRealizedPath p') =
        _root_.Path.Homotopic.Quotient.mk w.realizedPath
    rw [mk_normalizedRealizedPath_padNormalizedTo,
      normalize_realizedPath_class]
  · change _root_.Path.Homotopic.Quotient.mk
      (normalizedRealizedPath q') =
        _root_.Path.Homotopic.Quotient.mk w'.realizedPath
    rw [mk_normalizedRealizedPath_padNormalizedTo,
      normalize_realizedPath_class]

/-- Bottom and top signed-chain data with one common number of columns and
literal common endpoints. -/
structure BoundaryRows (X : SSet.{u}) (cols : ℕ)
    (leftVertex rightVertex : X _⦋0⦌) where
  bottom : SignedChain X cols leftVertex rightVertex
  top : SignedChain X cols leftVertex rightVertex

namespace CommonNormalization

/-- Regard a common normalization as prescribed bottom and top grid rows. -/
def boundaryRows {a b : SSet.FundamentalGroupoid X}
    {w w' : SSet.RealizationEdgeWord X a b} (c : CommonNormalization w w') :
    BoundaryRows X c.length (vertexRep a) (vertexRep b) :=
  ⟨c.left, c.right⟩

end CommonNormalization

namespace BoundaryRows

variable {cols rows : ℕ} {x y : X _⦋0⦌}

/-- Vertices of the prescribed bottom grid row. -/
def bottomVertex (B : BoundaryRows X cols x y) :
    Fin (cols + 1) → X _⦋0⦌ :=
  B.bottom.vertexAt

/-- Vertices of the prescribed top grid row. -/
def topVertex (B : BoundaryRows X cols x y) :
    Fin (cols + 1) → X _⦋0⦌ :=
  B.top.vertexAt

/-- Left-to-right signed edges of the prescribed bottom grid row. -/
def bottomHorizontal (B : BoundaryRows X cols x y) (c : Fin cols) :
    SSet.SignedEdge X (B.bottomVertex c.castSucc) (B.bottomVertex c.succ) :=
  B.bottom.edgeAt c

/-- Left-to-right signed edges of the prescribed top grid row. -/
def topHorizontal (B : BoundaryRows X cols x y) (c : Fin cols) :
    SSet.SignedEdge X (B.topVertex c.castSucc) (B.topVertex c.succ) :=
  B.top.edgeAt c

@[simp]
theorem bottom_left (B : BoundaryRows X cols x y) :
    B.bottomVertex 0 = x :=
  B.bottom.vertexAt_zero

@[simp]
theorem bottom_right (B : BoundaryRows X cols x y) :
    B.bottomVertex (Fin.last cols) = y :=
  B.bottom.vertexAt_last

@[simp]
theorem top_left (B : BoundaryRows X cols x y) :
    B.topVertex 0 = x :=
  B.top.vertexAt_zero

@[simp]
theorem top_right (B : BoundaryRows X cols x y) :
    B.topVertex (Fin.last cols) = y :=
  B.top.vertexAt_last

/-- Literal constant signed data for the left vertical boundary. -/
def leftVertical (_B : BoundaryRows X cols x y) (_r : Fin rows) :
    SSet.SignedEdge X x x :=
  SSet.SignedEdge.identity x

/-- Literal constant signed data for the right vertical boundary. -/
def rightVertical (_B : BoundaryRows X cols x y) (_r : Fin rows) :
    SSet.SignedEdge X y y :=
  SSet.SignedEdge.identity y

@[simp]
theorem leftVertical_toHom (B : BoundaryRows X cols x y) (r : Fin rows) :
    (B.leftVertical r).toHom = 𝟙 (SSet.FundamentalGroupoid.mk x) := by
  simp [leftVertical]

@[simp]
theorem rightVertical_toHom (B : BoundaryRows X cols x y) (r : Fin rows) :
    (B.rightVertical r).toHom = 𝟙 (SSet.FundamentalGroupoid.mk y) := by
  simp [rightVertical]

/-- A relation-only grid has the prescribed normalized bottom and top rows.
This proposition only constrains boundary data and does not assert that such a
grid exists. -/
structure FitsGrid (B : BoundaryRows X cols x y)
    (G : SSet.RelativeGridCertificate X rows cols) : Prop where
  bottom_vertex : ∀ c, G.vertex 0 c = B.bottomVertex c
  top_vertex : ∀ c, G.vertex (Fin.last rows) c = B.topVertex c
  bottom_horizontal : ∀ c, G.horizontal 0 c =
    SignedChain.castEdge (B.bottomHorizontal c)
      (bottom_vertex c.castSucc).symm (bottom_vertex c.succ).symm
  top_horizontal : ∀ c, G.horizontal (Fin.last rows) c =
    SignedChain.castEdge (B.topHorizontal c)
      (top_vertex c.castSucc).symm (top_vertex c.succ).symm
  left_endpoint : G.leftVertex = x
  right_endpoint : G.rightVertex = y

private theorem normalizedRow_eq_normalizedToHom
    (c : SignedChain X cols x y)
    (G : SSet.RelativeGridCertificate X rows cols)
    (r : Fin (rows + 1))
    (hvertex : ∀ j, G.vertex r j = c.vertexAt j)
    (hhorizontal : ∀ j, G.horizontal r j =
      SignedChain.castEdge (c.edgeAt j)
        (hvertex j.castSucc).symm (hvertex j.succ).symm)
    (hleft : G.leftVertex = x) (hright : G.rightVertex = y) :
    eqToHom (congrArg SSet.FundamentalGroupoid.mk hleft).symm ≫
        G.normalizedRow r ≫
        eqToHom (congrArg SSet.FundamentalGroupoid.mk hright) =
      normalizedToHom ⟨cols, c⟩ := by
  have hrows :
      ComposableArrows.mkOfObjOfMapSucc
          (fun j => SSet.FundamentalGroupoid.mk (G.vertex r j))
          (fun j => (G.horizontal r j).toHom) =
        c.toComposableArrows := by
    refine ComposableArrows.ext
      (fun j => congrArg SSet.FundamentalGroupoid.mk (hvertex j)) ?_
    intro i hi
    let j : Fin cols := ⟨i, hi⟩
    simp only [SignedChain.toComposableArrows,
      ComposableArrows.mkOfObjOfMapSucc_map_succ]
    change (G.horizontal r j).toHom =
      eqToHom (congrArg SSet.FundamentalGroupoid.mk
          (hvertex j.castSucc)) ≫
        (c.edgeAt j).toHom ≫
          eqToHom (congrArg SSet.FundamentalGroupoid.mk
            (hvertex j.succ)).symm
    rw [hhorizontal j, SignedChain.toHom_castEdge]
  have hrow : G.rowComposite r =
      eqToHom (congrArg SSet.FundamentalGroupoid.mk (hvertex 0)) ≫
        c.toComposableArrows.hom ≫
          eqToHom (congrArg SSet.FundamentalGroupoid.mk
            (hvertex (Fin.last cols))).symm := by
    unfold SSet.RelativeGridCertificate.rowComposite
    apply (conj_eqToHom_iff_heq _ _
      (congrArg SSet.FundamentalGroupoid.mk (hvertex 0))
      (congrArg SSet.FundamentalGroupoid.mk
        (hvertex (Fin.last cols)))).2
    have hhom := Functor.congr_hom hrows
      (homOfLE (show (0 : Fin (cols + 1)) ≤ Fin.last cols by simp))
    exact (conj_eqToHom_iff_heq _ _
      (Functor.congr_obj hrows 0)
      (Functor.congr_obj hrows (Fin.last cols))).1 hhom
  have houter :
      (eqToHom (congrArg SSet.FundamentalGroupoid.mk hleft).symm ≫
          G.normalizedRow r ≫
          eqToHom (congrArg SSet.FundamentalGroupoid.mk hright)) ≍
        G.normalizedRow r :=
    (conj_eqToHom_iff_heq _ _
      (congrArg SSet.FundamentalGroupoid.mk hleft).symm
      (congrArg SSet.FundamentalGroupoid.mk hright).symm).1 rfl
  have hnormalizedRow : G.normalizedRow r ≍ G.rowComposite r :=
    (conj_eqToHom_iff_heq _ _
      (congrArg SSet.FundamentalGroupoid.mk (G.left_vertex r)).symm
      (congrArg SSet.FundamentalGroupoid.mk (G.right_vertex r)).symm).1 rfl
  have hrow' : G.rowComposite r ≍ c.toComposableArrows.hom :=
    (conj_eqToHom_iff_heq _ _
      (congrArg SSet.FundamentalGroupoid.mk (hvertex 0))
      (congrArg SSet.FundamentalGroupoid.mk
        (hvertex (Fin.last cols)))).1 hrow
  have hchain : c.toComposableArrows.hom ≍ c.toHom :=
    (conj_eqToHom_iff_heq _ _
      (congrArg SSet.FundamentalGroupoid.mk c.vertexAt_zero)
      (congrArg SSet.FundamentalGroupoid.mk c.vertexAt_last)).1
        c.rowComposite_eq_toHom
  have hnormalized : normalizedToHom ⟨cols, c⟩ = c.toHom := by
    simp [normalizedToHom]
  exact eq_of_heq <|
    houter.trans <| hnormalizedRow.trans <| hrow'.trans <|
      hchain.trans (heq_of_eq hnormalized.symm)

/-- A relation-only grid fitting prescribed boundary rows reflects its
bottom-to-top telescope to equality of the represented normalized morphisms.
This is finite category algebra; it assumes rather than constructs the grid
and its triangle relations. -/
theorem FitsGridBoundaryReflection
    (B : BoundaryRows X cols x y)
    (G : SSet.RelativeGridCertificate X rows cols) (h : B.FitsGrid G) :
    normalizedToHom ⟨cols, B.bottom⟩ =
      normalizedToHom ⟨cols, B.top⟩ := by
  calc
    normalizedToHom ⟨cols, B.bottom⟩ =
        eqToHom (congrArg SSet.FundamentalGroupoid.mk
            h.left_endpoint).symm ≫
          G.normalizedRow 0 ≫
          eqToHom (congrArg SSet.FundamentalGroupoid.mk
            h.right_endpoint) :=
      (normalizedRow_eq_normalizedToHom B.bottom G 0 h.bottom_vertex
        h.bottom_horizontal h.left_endpoint h.right_endpoint).symm
    _ = eqToHom (congrArg SSet.FundamentalGroupoid.mk
            h.left_endpoint).symm ≫
          G.normalizedRow (Fin.last rows) ≫
          eqToHom (congrArg SSet.FundamentalGroupoid.mk
            h.right_endpoint) := by rw [G.bottomRow_eq_topRow]
    _ = normalizedToHom ⟨cols, B.top⟩ :=
      normalizedRow_eq_normalizedToHom B.top G (Fin.last rows) h.top_vertex
        h.top_horizontal h.left_endpoint h.right_endpoint

end BoundaryRows

end SSet.RealizationEdgeWord

end
