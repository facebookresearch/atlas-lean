/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monad.BarFunctorial
public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Ordinary simplicial replacement: strict Grothendieck-indexed prefix toward the two-sided bar

Given a small diagram `F : J ⥤ C` with `C` providing the needed coproducts, the ordinary
simplicial replacement has degree `n` equal to the coproduct of `F.obj s.left` over all
`n`-chains `s`. The indexing type `SrepIdx J n` is `ComposableArrows J n`;
informally this is intended as the fiber over `[n]` of the Grothendieck construction
of the nerve, but the formal API here constructs no Grothendieck object. No local
indexing, Grothendieck, or copower API is introduced; coproducts use the
`Limits.Sigma` interface.

Endpoint operators `srepFaceZero`, `srepFaceLast`, and `srepDegZero` are defined via
`Limits.Sigma.map'` from the endpoint index maps `δ₀`, `δlast`, and `precomp`,
with computation rules proved from `Limits.Sigma.ι_comp_map'`.

The matching `twoSidedBar` instantiation uses the identity monad: `srepLeftMod F` equips
`F` with its canonical left-module structure via `Functor.rightUnitor`, and
`srepRightMod` is the regular right module. At this instantiation bar degrees collapse
onto values of `F` (`barIdObjEq`, exposed as the isomorphism `barIdObjIso`), and the
`barData` / `barFace` / `barDegeneracy` / `barMap` view is recorded
(`bridgeDataObj`, `bridgeDataDelta`, `bridgeDataSigma`, `bridgeBarMapId`). The named
degreewise comparison `bridgeConstComp` maps each bar degree into the matching
replacement degree along constant chains. Comparisons are exposed as maps and
isomorphisms, never definitional identifications.

Strict prefix boundary. This file supplies only outer index maps and operators;
inner `Fin` omit/duplicate functors are in `StrictOmitDup` and are consumed by
the weighted-bar lane (`WeightedBarInner` / `WeightedBarData` /
`WeightedBarSimplicial`), not here. For the same reason, and because for fixed
plain-`Cat` data the bar degree depends on `n` solely through the monad power,
the fixed identity-monad construction here does not provide a general natural
isomorphism to `srepObj F` for arbitrary `J` and `F`; the isomorphism-level
bridge needs the profunctor/bicategorical encoding with its compatibility
data. `bridgeConstComp` is therefore a pointwise family, not a simplicial map.

No realization, homotopy colimit, model-categorical, derived, enriched, bicategorical,
or infinity-categorical claim is made.
-/

@[expose] public section

namespace CategoryTheory
namespace SrepBridge

universe vJ uJ vC uC

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]

/-- Indexing type for degree `n` of simplicial replacement: chains of `n` composable
arrows in `J`. Informally this is intended as the fiber over `[n]` of the Grothendieck
construction of the nerve; formally this is the `ComposableArrows` presentation
and constructs no Grothendieck object. No local indexing API is added. -/
abbrev SrepIdx (J : Type uJ) [Category.{vJ} J] (n : ℕ) := ComposableArrows J n

/-- Drop the first entry of a chain: the outermost-face index map. -/
def srepDropFirst {n : ℕ} (s : SrepIdx J (n + 1)) : SrepIdx J n := s.δ₀

/-- Dropping the first entry exposes the second entry definitionally. -/
theorem srepDropFirst_left {n : ℕ} (s : SrepIdx J (n + 1)) :
    (srepDropFirst s).left = s.obj' 1 := rfl

/-- Drop the last entry of a chain: the other outermost-face index map. -/
def srepDropLast {n : ℕ} (s : SrepIdx J (n + 1)) : SrepIdx J n := s.δlast

/-- Dropping the last entry preserves the left endpoint definitionally. -/
theorem srepDropLast_left {n : ℕ} (s : SrepIdx J (n + 1)) :
    (srepDropLast s).left = s.left := rfl

/-- Repeat the first entry: the outermost-degeneracy index map, via `precomp` with the
identity. -/
def srepDupFirst {n : ℕ} (s : SrepIdx J n) : SrepIdx J (n + 1) :=
  s.precomp (𝟙 s.left)

/-- Repeating the first entry preserves the left endpoint definitionally. -/
theorem srepDupFirst_left {n : ℕ} (s : SrepIdx J n) :
    (srepDupFirst s).left = s.left := rfl

/-- The left endpoint is the zeroth vertex. -/
theorem srepLeftZero {n : ℕ} (s : SrepIdx J n) : s.left = s.obj ⟨0, by omega⟩ := rfl

/-- Degree `n` of simplicial replacement: the coproduct of the values of `F` at the left
endpoints of all `n`-chains. -/
noncomputable def srepObj (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun s : SrepIdx J n => F.obj s.left)] : C :=
  ∐ fun s : SrepIdx J n => F.obj s.left

/-- Inclusion of the summand indexed by `s`. -/
noncomputable def srepIncl (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun s : SrepIdx J n => F.obj s.left)] (s : SrepIdx J n) :
    F.obj s.left ⟶ srepObj F n :=
  Limits.Sigma.ι (fun s : SrepIdx J n => F.obj s.left) s

/-- Universal map out of a replacement degree from component maps. -/
noncomputable def srepDesc (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun s : SrepIdx J n => F.obj s.left)] {P : C}
    (p : ∀ s : SrepIdx J n, F.obj s.left ⟶ P) : srepObj F n ⟶ P :=
  Limits.Sigma.desc p

/-- Computation rule for `srepDesc`. -/
theorem srepDesc_ι (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun s : SrepIdx J n => F.obj s.left)] {P : C}
    (p : ∀ s : SrepIdx J n, F.obj s.left ⟶ P) (s : SrepIdx J n) :
    srepIncl F n s ≫ srepDesc F n p = p s :=
  Limits.Sigma.ι_comp_desc p s

/-- Functoriality of replacement degrees in the diagram. -/
noncomputable def srepMap {F G : J ⥤ C} (n : ℕ)
    [Limits.HasCoproduct (fun s : SrepIdx J n => F.obj s.left)]
    [Limits.HasCoproduct (fun s : SrepIdx J n => G.obj s.left)] (φ : F ⟶ G) :
    srepObj F n ⟶ srepObj G n :=
  Limits.Sigma.map (fun s : SrepIdx J n => φ.app s.left)

/-- Computation rule for `srepMap`. -/
theorem srepMap_ι {F G : J ⥤ C} (n : ℕ)
    [Limits.HasCoproduct (fun s : SrepIdx J n => F.obj s.left)]
    [Limits.HasCoproduct (fun s : SrepIdx J n => G.obj s.left)]
    (φ : F ⟶ G) (s : SrepIdx J n) :
    srepIncl F n s ≫ srepMap n φ = φ.app s.left ≫ srepIncl G n s :=
  Limits.Sigma.ι_map (fun s : SrepIdx J n => φ.app s.left) s

/-- `srepMap` preserves identities. -/
theorem srepMap_id (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun s : SrepIdx J n => F.obj s.left)] :
    srepMap n (𝟙 F) = 𝟙 (srepObj F n) := by
  change Limits.Sigma.map (fun s : SrepIdx J n => 𝟙 (F.obj s.left)) = 𝟙 (srepObj F n)
  exact Limits.Sigma.map_id

/-- `srepMap` preserves composition. -/
theorem srepMap_comp {F G H : J ⥤ C} (n : ℕ)
    [Limits.HasCoproduct (fun s : SrepIdx J n => F.obj s.left)]
    [Limits.HasCoproduct (fun s : SrepIdx J n => G.obj s.left)]
    [Limits.HasCoproduct (fun s : SrepIdx J n => H.obj s.left)]
    (φ : F ⟶ G) (ψ : G ⟶ H) :
    srepMap n φ ≫ srepMap n ψ = srepMap n (φ ≫ ψ) := by
  change Limits.Sigma.map (fun s : SrepIdx J n => φ.app s.left) ≫
      Limits.Sigma.map (fun s : SrepIdx J n => ψ.app s.left) =
    Limits.Sigma.map (fun s : SrepIdx J n => φ.app s.left ≫ ψ.app s.left)
  exact Limits.Sigma.map_comp_map _ _

/-- Component map of the outermost face `d₀` at the chain `s`: act by the first arrow,
transported along the definitional endpoint identifications. -/
def srepFaceZeroComponent (F : J ⥤ C) {n : ℕ} (s : SrepIdx J (n + 1)) :
    F.obj s.left ⟶ F.obj ((srepDropFirst s).left) :=
  eqToHom (congrArg F.obj (srepLeftZero s)) ≫ F.map (s.map' 0 1) ≫
    eqToHom (congrArg F.obj (srepDropFirst_left s).symm)

/-- Outermost face `d₀`: drop the first entry of each chain, acting by its first arrow. -/
noncomputable def srepFaceZero (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun s : SrepIdx J (n + 1) => F.obj s.left)]
    [Limits.HasCoproduct (fun s : SrepIdx J n => F.obj s.left)] :
    srepObj F (n + 1) ⟶ srepObj F n :=
  Limits.Sigma.map' srepDropFirst fun s => srepFaceZeroComponent F s

/-- Computation rule for `srepFaceZero`. -/
theorem srepFaceZero_ι (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun s : SrepIdx J (n + 1) => F.obj s.left)]
    [Limits.HasCoproduct (fun s : SrepIdx J n => F.obj s.left)]
    (s : SrepIdx J (n + 1)) :
    srepIncl F (n + 1) s ≫ srepFaceZero F n =
      srepFaceZeroComponent F s ≫ srepIncl F n (srepDropFirst s) := by
  change Limits.Sigma.ι (fun s : SrepIdx J (n + 1) => F.obj s.left) s ≫
      Limits.Sigma.map' srepDropFirst (fun s : SrepIdx J (n + 1) =>
        srepFaceZeroComponent F s) =
    srepFaceZeroComponent F s ≫
      Limits.Sigma.ι (fun s : SrepIdx J n => F.obj s.left) (srepDropFirst s)
  exact Limits.Sigma.ι_comp_map' _ _ _

/-- Component map of the outermost face `d_last` at `s`: the identity on values, since
dropping the last entry fixes the left endpoint. -/
def srepFaceLastComponent (F : J ⥤ C) {n : ℕ} (s : SrepIdx J (n + 1)) :
    F.obj s.left ⟶ F.obj ((srepDropLast s).left) :=
  eqToHom (congrArg F.obj (srepDropLast_left s).symm)

/-- Outermost face `d_last`: drop the last entry of each chain. -/
noncomputable def srepFaceLast (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun s : SrepIdx J (n + 1) => F.obj s.left)]
    [Limits.HasCoproduct (fun s : SrepIdx J n => F.obj s.left)] :
    srepObj F (n + 1) ⟶ srepObj F n :=
  Limits.Sigma.map' srepDropLast fun s => srepFaceLastComponent F s

/-- Computation rule for `srepFaceLast`. -/
theorem srepFaceLast_ι (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun s : SrepIdx J (n + 1) => F.obj s.left)]
    [Limits.HasCoproduct (fun s : SrepIdx J n => F.obj s.left)]
    (s : SrepIdx J (n + 1)) :
    srepIncl F (n + 1) s ≫ srepFaceLast F n =
      srepFaceLastComponent F s ≫ srepIncl F n (srepDropLast s) := by
  change Limits.Sigma.ι (fun s : SrepIdx J (n + 1) => F.obj s.left) s ≫
      Limits.Sigma.map' srepDropLast (fun s : SrepIdx J (n + 1) =>
        srepFaceLastComponent F s) =
    srepFaceLastComponent F s ≫
      Limits.Sigma.ι (fun s : SrepIdx J n => F.obj s.left) (srepDropLast s)
  exact Limits.Sigma.ι_comp_map' _ _ _

/-- Component map of the outermost degeneracy `s₀` at `s`: the identity on values, since
repeating the first entry fixes the left endpoint. -/
def srepDegZeroComponent (F : J ⥤ C) {n : ℕ} (s : SrepIdx J n) :
    F.obj s.left ⟶ F.obj ((srepDupFirst s).left) :=
  eqToHom (congrArg F.obj (srepDupFirst_left s).symm)

/-- Outermost degeneracy `s₀`: repeat the first entry of each chain. -/
noncomputable def srepDegZero (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun s : SrepIdx J n => F.obj s.left)]
    [Limits.HasCoproduct (fun s : SrepIdx J (n + 1) => F.obj s.left)] :
    srepObj F n ⟶ srepObj F (n + 1) :=
  Limits.Sigma.map' srepDupFirst fun s => srepDegZeroComponent F s

/-- Computation rule for `srepDegZero`. -/
theorem srepDegZero_ι (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun s : SrepIdx J n => F.obj s.left)]
    [Limits.HasCoproduct (fun s : SrepIdx J (n + 1) => F.obj s.left)]
    (s : SrepIdx J n) :
    srepIncl F n s ≫ srepDegZero F n =
      srepDegZeroComponent F s ≫ srepIncl F (n + 1) (srepDupFirst s) := by
  change Limits.Sigma.ι (fun s : SrepIdx J n => F.obj s.left) s ≫
      Limits.Sigma.map' srepDupFirst (fun s : SrepIdx J n =>
        srepDegZeroComponent F s) =
    srepDegZeroComponent F s ≫
      Limits.Sigma.ι (fun s : SrepIdx J (n + 1) => F.obj s.left) (srepDupFirst s)
  exact Limits.Sigma.ι_comp_map' _ _ _

/-- The identity monad acts as the identity functor. -/
theorem idMonadFunctor : (Monad.id C).toFunctor = 𝟭 C := rfl

/-- The unit of the identity monad is the identity transformation. -/
theorem idMonadEta : (Monad.id C).η = 𝟙 (𝟭 C) := rfl

/-- The multiplication of the identity monad is the identity transformation. -/
theorem idMonadMu : (Monad.id C).μ = 𝟙 (𝟭 C) := rfl

/-- Every diagram carries a canonical left-module structure over the identity monad,
given by the right unitor. This is the matching left-module instantiation. -/
def srepLeftMod (F : J ⥤ C) : Monad.LeftModule J (Monad.id C) :=
  Monad.LeftModule.mk (T := Monad.id C) F (Functor.rightUnitor F).hom
    (fun X => Category.id_comp ((Functor.rightUnitor F).hom.app X))
    (fun _ => rfl)

/-- The matching left module lies over `F`. -/
theorem srepLeftMod_functor (F : J ⥤ C) : (srepLeftMod F).functor = F := rfl

/-- The matching right module is the regular module over the identity monad. -/
def srepRightMod : Monad.RightModule (Monad.id C) C :=
  Monad.RightModule.regular (Monad.id C)

/-- The matching right module acts as the identity functor. -/
theorem srepRightMod_functor : srepRightMod.functor = (Monad.id C).toFunctor := rfl

/-- Powers of the identity monad fix every object. -/
theorem barPowIdObj (n : ℕ) (X : C) : (Monad.monadPow (Monad.id C) n).obj X = X := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- Degreewise objects of the matching bar are propositionally the values of `F`. -/
theorem barIdObjEq (F : J ⥤ C) (n : ℕ) (a : J) :
    (Monad.barObj (Monad.id C) srepRightMod (srepLeftMod F) n).obj a = F.obj a := by
  simp only [Monad.barObj_obj, srepLeftMod_functor, srepRightMod_functor, idMonadFunctor,
    Functor.id_obj, barPowIdObj]

/-- The degreewise identification as an isomorphism, never a definitional
identification. -/
def barIdObjIso (F : J ⥤ C) (n : ℕ) (a : J) :
    (Monad.barObj (Monad.id C) srepRightMod (srepLeftMod F) n).obj a ≅ F.obj a :=
  eqToIso (barIdObjEq F n a)

/-- Constant chains: every object sits inside every replacement degree. -/
def constChain (a : J) (n : ℕ) : SrepIdx J n := (Functor.const (Fin (n + 1))).obj a

/-- Constant chains start at their object. -/
theorem constChain_left (a : J) (n : ℕ) : (constChain a n).left = a := rfl

/-- Constant chains lie over their object. -/
theorem constChainEq (F : J ⥤ C) (n : ℕ) (a : J) :
    F.obj a = F.obj ((constChain a n).left) := by
  rw [constChain_left]

/-- Named degreewise comparison: bar degrees map into replacement degrees along constant
chains. This is a pointwise family, not a simplicial map: a simplicial comparison
would require the appropriate profunctor/bicategorical encoding with its
compatibility data. -/
noncomputable def bridgeConstComp (F : J ⥤ C) (n : ℕ)
    [Limits.HasCoproduct (fun s : SrepIdx J n => F.obj s.left)] (a : J) :
    (Monad.barObj (Monad.id C) srepRightMod (srepLeftMod F) n).obj a ⟶ srepObj F n :=
  eqToHom (barIdObjEq F n a) ≫ eqToHom (constChainEq F n a) ≫
    Limits.Sigma.ι (fun s : SrepIdx J n => F.obj s.left) (constChain a n)

/-- Data-level view of the matching bar degrees. -/
theorem bridgeDataObj (F : J ⥤ C) (n : ℕ) :
    (Monad.barData (Monad.id C) srepRightMod (srepLeftMod F)).obj n =
      Monad.barObj (Monad.id C) srepRightMod (srepLeftMod F) n :=
  Monad.barData_obj_n _ _ _ n

/-- Data-level faces of the matching bar are the `barFace` operators. -/
theorem bridgeDataDelta (F : J ⥤ C) {n : ℕ} (i : Fin (n + 2)) :
    (Monad.barData (Monad.id C) srepRightMod (srepLeftMod F)).δ i =
      Monad.barFace n i :=
  Monad.barData_δ _ _ _ _

/-- Data-level degeneracies of the matching bar are the `barDegeneracy`
operators. -/
theorem bridgeDataSigma (F : J ⥤ C) {n : ℕ} (i : Fin (n + 1)) :
    (Monad.barData (Monad.id C) srepRightMod (srepLeftMod F)).σ i =
      Monad.barDegeneracy n i :=
  Monad.barData_σ _ _ _ _

/-- The bar-side functoriality used by the bridge is `barMap`; at the matching
instantiation its identity law is exactly the `barMap_id` law, so no simplicial
identity is re-proved here. -/
theorem bridgeBarMapId (F : J ⥤ C) (n : ℕ) :
    Monad.barMap (𝟙 srepRightMod) (𝟙 (srepLeftMod F)) n =
      𝟙 (Monad.barObj (Monad.id C) srepRightMod (srepLeftMod F) n) :=
  Monad.barMap_id _ _ _

end SrepBridge
end CategoryTheory
