/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.SigmaComponent
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Full componentwise maps of sigma spaces

A componentwise continuous map between sigma spaces induces a full
fundamental-groupoid functor when every source component is path connected
and every target component is simply connected.  It is essentially
surjective when every source component is nonempty and every target
component is path connected.  These statements apply in particular to
componentwise subtype inclusions.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology

universe u v w

namespace FundamentalGroupoid.SigmaSubtype

variable {ι : Type u} (A : ι → Type v) (B : ι → Type w)
variable [∀ i, TopologicalSpace (A i)] [∀ i, TopologicalSpace (B i)]

/-- Assemble continuous maps with a common index into the corresponding
map of sigma spaces. -/
def map (f : ∀ i, C(A i, B i)) : C((Σ i, A i), (Σ i, B i)) where
  toFun z := ⟨z.1, f z.1 z.2⟩
  continuous_toFun := by
    apply continuous_sigma
    intro i
    exact continuous_sigmaMk.comp (f i).continuous

/-- The componentwise sigma map retains its original index and applies the
selected component map to its original point. -/
@[simp]
theorem map_apply (f : ∀ i, C(A i, B i)) (i : ι) (a : A i) :
    map A B f ⟨i, a⟩ = ⟨i, f i a⟩ :=
  rfl

/-- Any map from a path-connected space to a simply connected space is full
on fundamental groupoids. -/
theorem mapFullOfPathConnectedSimplyConnected
    {S : Type v} {T : Type w} [TopologicalSpace S] [TopologicalSpace T]
    [PathConnectedSpace S] [SimplyConnectedSpace T] (f : C(S, T)) :
    (FundamentalGroupoid.map f).Full where
  map_surjective {a b} q := by
    let p : Path.Homotopic.Quotient a.as b.as :=
      Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath a.as b.as)
    refine ⟨p, ?_⟩
    change p.map f = q
    exact Subsingleton.elim _ _

/-- A componentwise sigma map is full when each source component is path
connected and each target component is simply connected. -/
theorem mapFull (f : ∀ i, C(A i, B i))
    [∀ i, PathConnectedSpace (A i)] [∀ i, SimplyConnectedSpace (B i)] :
    (FundamentalGroupoid.map (map A B f)).Full where
  map_surjective {a b} q := by
    rcases a with ⟨⟨i, a⟩⟩
    rcases b with ⟨⟨j, b⟩⟩
    have hij := FundamentalGroupoid.SigmaComponent.hom_index_eq B q
    change i = j at hij
    subst j
    let p : Path.Homotopic.Quotient a b :=
      Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath a b)
    let iA := FundamentalGroupoid.SigmaComponent.inclusion A i
    let iB := FundamentalGroupoid.SigmaComponent.inclusion B i
    let qB : FundamentalGroupoid.mk (f i a) ⟶ FundamentalGroupoid.mk (f i b) :=
      (FundamentalGroupoid.SigmaComponent.fullyFaithful B i).preimage q
    have hqB : (FundamentalGroupoid.map (f i)).map p = qB := by
      change p.map (f i) = qB
      exact Subsingleton.elim _ _
    change p.map (f i) = qB at hqB
    refine ⟨(FundamentalGroupoid.map iA).map p, ?_⟩
    change ((p.map iA).map (map A B f)) = q
    have hpmap : (p.map iA).map (map A B f) = (p.map (f i)).map iB := by
      induction p using Path.Homotopic.Quotient.ind with
      | mk path => rfl
    rw [hpmap, hqB]
    exact (FundamentalGroupoid.SigmaComponent.fullyFaithful B i).map_preimage q

/-- A componentwise sigma map is essentially surjective when every source
component is nonempty and every target component is path connected. -/
theorem mapEssSurj (f : ∀ i, C(A i, B i))
    [∀ i, Nonempty (A i)] [∀ i, PathConnectedSpace (B i)] :
    (FundamentalGroupoid.map (map A B f)).EssSurj where
  mem_essImage := by
    rintro ⟨⟨i, b⟩⟩
    let a : A i := Classical.choice (inferInstance : Nonempty (A i))
    let p : Path (f i a) b := PathConnectedSpace.somePath (f i a) b
    let h : FundamentalGroupoid.mk (Sigma.mk i (f i a)) ⟶
        FundamentalGroupoid.mk (Sigma.mk i b) :=
      (Path.Homotopic.Quotient.mk p).map
        (FundamentalGroupoid.SigmaComponent.inclusion B i)
    exact ⟨FundamentalGroupoid.mk (Sigma.mk i a),
      ⟨(Groupoid.isoEquivHom _ _).symm h⟩⟩

end FundamentalGroupoid.SigmaSubtype

end

end
