/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCriticalDiagram
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCriticalRootHorn

/-!
# The same original terminal horn as a full critically marked subdiagram

At the original root retain every original upper coordinate and every
nonterminal lower coordinate with exactly the critical cone's inherited
marking. Above the root retain each whole original critical coefficient.
The original path-union action preserves these exact supports and marks,
giving the full genuine marked enriched horn and original inclusion.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- Every original terminal horn coefficient retains its same whole original support and precisely the marking
pulled back from its actual critical cone coefficient. -/
def coneCriticalHornWeight (n : ℕ) (i : Vertex.{u} (n + 2)) : Marked.{u} :=
  comap (coneCriticalWeight n i) (coneRootHornSupport (Fin.last (n + 2)) i).ι

/-- Each entire original critically marked horn coefficient enters the SAME whole original critical cone by its
literal supported inclusion. -/
def coneCriticalHornCoefficientInclusion (n : ℕ) (i : Vertex.{u} (n + 2)) :
    coneCriticalHornWeight n i ⟶ coneCriticalWeight n i :=
  comapHom (coneCriticalWeight n i) (coneRootHornSupport (Fin.last (n + 2)) i).ι

/-- The SAME original critical horn inclusion is monic on every complete original supported coefficient. -/
instance coneCriticalHornCoefficientInclusion_mono (n : ℕ) (i : Vertex.{u} (n + 2)) :
    Mono (coneCriticalHornCoefficientInclusion n i) :=
  (mono_iff_underlying _).mpr (inferInstance : Mono (coneRootHornSupport (Fin.last (n + 2)) i).ι)

/-- Every complete original path action restricts to the SAME terminal horn support with its exact original
inherited critical marker. -/
def coneCriticalHornAction (n : ℕ) (i j : Vertex.{u} (n + 2)) :
    prod (max (nerve (SimplicialThickening.Path i j))) (coneCriticalHornWeight n j) ⟶ coneCriticalHornWeight n i where
  hom :=
    { app q := ↾fun x => ⟨(coneCriticalAction n i j).hom.app q (x.1, x.2.val),
        coneRootHornSupport_action_mem (Fin.last (n + 2)) i j q x.1 x.2.val x.2.property⟩
      naturality q r f := by
        apply ConcreteCategory.hom_ext
        intro x
        apply Subtype.ext
        exact congr($((coneCriticalAction n i j).hom.naturality f) (x.1, x.2.val)) }
  preserve {e} he := (coneCriticalAction n i j).preserve (show
    (e.1, e.2.val) ∈ (prod (max (nerve (SimplicialThickening.Path i j))) (coneCriticalWeight n j)).marking from
      ⟨he.1, he.2⟩)

/-- The complete SAME original critically marked terminal horn is its genuine whole enriched subdiagram, retaining
all original path identities and compositions. -/
def coneCriticalHornDiagram (n : ℕ) : EnrichedDiagram (Index.{u} (n + 2))ᵒᵖ where
  obj i := coneCriticalHornWeight n i.unop.as
  map i j := maxCurry (coneCriticalHornAction n j.unop.as i.unop.as)
  map_id i := by
    ext q z
    apply Hom.ext
    ext r a
    apply Subtype.ext
    refine CategoryTheory.Functor.ext (fun t => ConeSubset.prepend_id _) (fun _ _ _ => Subsingleton.elim _ _)
  map_comp i j m := by
    ext q fg
    apply Hom.ext
    ext r a
    apply Subtype.ext
    refine CategoryTheory.Functor.ext (fun t => (ConeSubset.prepend_comp _ _ _).symm)
      (fun _ _ _ => Subsingleton.elim _ _)

/-- The SAME entire original marked enriched terminal horn enters the complete critically marked cone through its
exact whole supported inclusions. -/
def coneCriticalHornInclusion (n : ℕ) : coneCriticalHornDiagram.{u} n ⟶ coneCriticalDiagram n where
  app i := coneCriticalHornCoefficientInclusion n i.unop.as
  naturality i j := by
    ext q p
    apply Hom.ext
    ext r a
    rfl

/-- The actual original root of the full critical horn is precisely the SAME entire critically marked original
coordinate horn. -/
def coneCriticalHornRootIso (n : ℕ) :
    coneCriticalHornWeight n (⊥ : Vertex.{u} (n + 2)) ≅ coneCriticalRootHornMarked.{u} n :=
  isoMk (Subcomplex.eqToIso (coneRootHornSupport_root (Fin.last (n + 2)))) (fun _ => Iff.rfl)

/-- The actual entire root coefficient isomorphism retains the SAME literal original critical marked horn attaching
map. -/
theorem coneCriticalHornRootIso_inclusion (n : ℕ) :
    (coneCriticalHornRootIso.{u} n).hom ≫ coneCriticalRootHornMap n =
      coneCriticalHornCoefficientInclusion n (⊥ : Vertex.{u} (n + 2)) := Hom.ext rfl

/-- At every original coefficient above root the SAME complete critically marked horn support is the actual whole
original marked coefficient isomorphism. -/
def coneCriticalHornAboveIso (n : ℕ) {i : Vertex.{u} (n + 2)} (hi : (⊥ : Vertex.{u} (n + 2)) < i) :
    coneCriticalHornWeight n i ≅ coneCriticalWeight n i :=
  isoMk (Subcomplex.eqToIso (coneRootHornSupport_above (Fin.last (n + 2)) hi) ≪≫
    Subcomplex.topIso (nerve (ConeSubset i))) (fun _ => Iff.rfl)

/-- The original complete positive critical coefficient isomorphism retains exactly the SAME literal original horn
inclusion. -/
theorem coneCriticalHornAboveIso_hom (n : ℕ) {i : Vertex.{u} (n + 2)} (hi : (⊥ : Vertex.{u} (n + 2)) < i) :
    (coneCriticalHornAboveIso n hi).hom = coneCriticalHornCoefficientInclusion n i := Hom.ext rfl

end SSet.Marked.CoherentWeight
