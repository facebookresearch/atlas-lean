/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.DirectLimit
public import MathlibExt.Analysis.CStarAlgebra.NonUnitalCompletion
public import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Completed isometric limits of C-star algebras

For a nonempty directed preordered index type, let `S_i` be nonunital C-star algebras with
coherent complex nonunital star connecting maps preserving every stage norm. The algebraic
direct limit has `‖[i,x]‖ = ‖x‖`, and its uniform completion is a nonunital C-star algebra. The
stage maps are isometric, injective, compatible with connecting maps and have dense union.

Compatible star homomorphisms `g_i : S_i → C` into a nonunital C-star algebra extend uniquely to
the completed limit. The extension is contractive. If each `g_i` preserves norms, the extension
does too and is injective; if the extension is injective and the union of the stage images is
dense in `C`, it is surjective. Zero stage and limit algebras are permitted.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace CStarAlgebra.DirectLimit

universe uI uA uC

/-- **Isometric system of C-star algebras.** On a preordered type `I`, this record contains
nonunital C-star stages `S_i` and complex nonunital star maps `S_i → S_j` for `i ≤ j`, with
identity/composition coherence and `‖S_ij x‖ = ‖x‖`. -/
structure IsometricSystem (I : Type uI) [Preorder I] where
  /-- **Stage algebras of the system.** The family `Stage : I → Type` gives one coefficient
  carrier for every preordered index. -/
  Stage : I → Type uA
  /-- **C-star structure of each stage.** Every stage has a nonunital complex C-star algebra
  structure, including its complete normed-space structure. -/
  [stageCStarAlgebra : ∀ i, NonUnitalCStarAlgebra (Stage i)]
  /-- **Connecting star homomorphisms.** For `i ≤ j`, the map `Stage i → Stage j` is a complex
  nonunital star-algebra homomorphism. -/
  map : ∀ i j, i ≤ j → Stage i →⋆ₙₐ[ℂ] Stage j
  /-- **Identity connecting map.** The map at `i ≤ i` equals `NonUnitalStarAlgHom.id ℂ (Stage i)`. -/
  map_refl : ∀ i, map i i le_rfl = NonUnitalStarAlgHom.id ℂ (Stage i)
  /-- **Composition of connecting maps.** For `i ≤ j ≤ k`, the connecting map from `i` to `k` is
  the composite of those from `i` to `j` and `j` to `k`. -/
  map_trans : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k),
    (map j k hjk).comp (map i j hij) = map i k (hij.trans hjk)
  /-- **Isometric connecting maps.** Every connecting map satisfies `‖map i j hij x‖ = ‖x‖` on its
  source stage. -/
  norm_map : ∀ i j (hij : i ≤ j) x, ‖map i j hij x‖ = ‖x‖

attribute [instance] IsometricSystem.stageCStarAlgebra

namespace IsometricSystem

variable {I : Type uI} [Preorder I] [IsDirectedOrder I] [Nonempty I]

instance directedSystem (S : IsometricSystem.{uI, uA} I) :
    DirectedSystem S.Stage (S.map · · ·) where
  map_self := fun {i} x => DFunLike.congr_fun (S.map_refl i) x
  map_map := fun {_k _j _i} hij hjk x => DFunLike.congr_fun (S.map_trans hij hjk) x

/-- **Algebraic limit of an isometric system.** For a nonempty directed preordered index and an
isometric C-star system `S`, `Raw S` is the algebraic direct limit, with each representative
`[i,x]` having norm `‖x‖`. -/
abbrev Raw (S : IsometricSystem.{uI, uA} I) :=
  _root_.DirectLimit S.Stage S.map

noncomputable instance rawNormedRing (S : IsometricSystem.{uI, uA} I) :
    NonUnitalNormedRing S.Raw :=
  _root_.DirectLimit.nonUnitalNormedRingOfNormPreserving S.map S.norm_map

noncomputable instance rawNormedSpace (S : IsometricSystem.{uI, uA} I) :
    NormedSpace ℂ S.Raw :=
  _root_.DirectLimit.normedSpaceOfNormPreserving (𝕜 := ℂ) S.map S.norm_map

noncomputable instance rawCStarRing (S : IsometricSystem.{uI, uA} I) :
    CStarRing S.Raw :=
  _root_.DirectLimit.cstar_ring_of_norm_preserving S.map S.norm_map

/-- **Completion of the isometric algebraic limit.** For a nonempty directed isometric C-star
system, `Completed S` is the uniform completion of `S.Raw` with its descended stage norm. -/
abbrev Completed (S : IsometricSystem.{uI, uA} I) :=
  UniformSpace.Completion S.Raw

noncomputable instance completedCStarAlgebra (S : IsometricSystem.{uI, uA} I) :
    NonUnitalCStarAlgebra S.Completed :=
  CStarAlgebra.completionNonUnitalCStarAlgebra S.Raw

/-- **Algebraic stage inclusion.** For a nonempty directed isometric C-star system, `rawOf S i` is
the complex nonunital star map sending `x : S.Stage i` to the direct-limit class `[i,x]`. -/
def rawOf (S : IsometricSystem.{uI, uA} I) (i : I) : S.Stage i →⋆ₙₐ[ℂ] S.Raw where
  toNonUnitalAlgHom := _root_.DirectLimit.NonUnitalAlgebra.of S.Stage S.map i
  map_star' x := (_root_.DirectLimit.star_def (f := S.map) i x).symm

/-- **Completed stage inclusion.** For a nonempty directed isometric C-star system, `of S i` sends
`x : S.Stage i` to the completion image of `[i,x]`. -/
def of (S : IsometricSystem.{uI, uA} I) (i : I) : S.Stage i →⋆ₙₐ[ℂ] S.Completed where
  toFun x := (S.rawOf i x : S.Completed)
  map_zero' := by
    rw [map_zero, UniformSpace.Completion.coe_zero]
  map_add' x y := by
    rw [map_add, UniformSpace.Completion.coe_add]
  map_mul' x y := by
    rw [map_mul, UniformSpace.Completion.nonUnitalCompletion_coe_mul S.Raw]
  map_smul' c x := by
    simp only [map_smul, UniformSpace.Completion.coe_smul, MonoidHom.coe_id, id]
  map_star' x := by
    rw [map_star, CStarAlgebra.completionNonUnitalCStarAlgebra_star_coe S.Raw]

/-- **Norm preservation of a stage inclusion.** For an isometric C-star system on a nonempty
directed index, `‖S.of i x‖ = ‖x‖`. -/
@[simp]
theorem norm_of (S : IsometricSystem.{uI, uA} I) (i : I) (x : S.Stage i) :
    ‖S.of i x‖ = ‖x‖ := by
  change ‖(S.rawOf i x : S.Completed)‖ = ‖x‖
  rw [UniformSpace.Completion.norm_coe]
  exact _root_.DirectLimit.normedAddCommGroupOfNormPreserving_norm_mk S.map S.norm_map i x

/-- **Injective completed stage map.** Every stage inclusion `S.of i` of a nonempty directed
isometric C-star system is injective. -/
theorem of_injective (S : IsometricSystem.{uI, uA} I) (i : I) :
    Function.Injective (S.of i) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [← S.norm_of i (x - y), map_sub, hxy, sub_self, norm_zero]

/-- **Compatibility of completed stage inclusions.** For `i ≤ j`, `S.of j (S.map i j hij x) = S.of
i x`. -/
@[simp]
theorem of_map (S : IsometricSystem.{uI, uA} I) {i j : I}
    (hij : i ≤ j) (x : S.Stage i) : S.of j (S.map i j hij x) = S.of i x := by
  change ((_root_.DirectLimit.NonUnitalAlgebra.of S.Stage S.map j
      (S.map i j hij x) : S.Raw) : S.Completed) =
    ((_root_.DirectLimit.NonUnitalAlgebra.of S.Stage S.map i x : S.Raw) : S.Completed)
  exact congrArg (fun z : S.Raw => (z : S.Completed))
    (_root_.DirectLimit.NonUnitalAlgebra.of_f (G := S.Stage) (f := S.map) hij x)

/-- **Density of the stage images.** For a nonempty directed isometric C-star system, `⋃ i,
Set.range (S.of i)` is dense in the completed limit. -/
theorem dense_union_range (S : IsometricSystem.{uI, uA} I) :
    Dense (⋃ i, Set.range (S.of i)) := by
  have hset : (⋃ i, Set.range (S.of i)) =
      Set.range (fun z : S.Raw => (z : S.Completed)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      obtain ⟨x, rfl⟩ := hi
      exact ⟨S.rawOf i x, rfl⟩
    · rintro ⟨x, rfl⟩
      refine _root_.DirectLimit.induction (f := S.map) (fun i a => ?_) x
      exact Set.mem_iUnion.mpr ⟨i, ⟨a, rfl⟩⟩
  rw [hset]
  exact UniformSpace.Completion.denseRange_coe

section Universal

-- Keep raw linear maps on the topology of their constructed norm uniformity.
attribute [local instance 2000] UniformSpace.toTopologicalSpace

variable (S : IsometricSystem.{uI, uA} I)
  {C : Type uC} [NonUnitalCStarAlgebra C]
  (g : ∀ i, S.Stage i →⋆ₙₐ[ℂ] C)
  (hg : ∀ {i j : I} (hij : i ≤ j), (g j).comp (S.map i j hij) = g i)

/-- **Universal algebraic limit map.** Compatible complex nonunital star maps `g_i : S.Stage i →
C` into a C-star algebra define the star homomorphism `S.Raw → C` determined by `[i,x] ↦
g_i(x)`. -/
def rawLift : S.Raw →⋆ₙₐ[ℂ] C where
  toNonUnitalAlgHom := _root_.DirectLimit.NonUnitalAlgebra.lift S.Stage S.map C
    (fun i => (g i).toNonUnitalAlgHom)
    (fun i j hij x => DFunLike.congr_fun (hg hij) x)
  map_star' x := by
    refine _root_.DirectLimit.induction (f := S.map) (fun i a => ?_) x
    rw [_root_.DirectLimit.star_def]
    change g i (star a) = star (g i a)
    exact map_star (g i) a

@[simp]
theorem rawLift_rawOf (i : I) (x : S.Stage i) : S.rawLift g hg (S.rawOf i x) = g i x :=
  rfl

/-- **Contractivity of the algebraic universal map.** For compatible C-star stage homomorphisms
`g_i`, `‖S.rawLift g hg x‖ ≤ ‖x‖` on the descended algebraic limit norm. -/
theorem norm_rawLift_le (x : S.Raw) : ‖S.rawLift g hg x‖ ≤ ‖x‖ := by
  refine _root_.DirectLimit.induction (f := S.map) (fun i a => ?_) x
  change ‖g i a‖ ≤ ‖(⟦⟨i, a⟩⟧ : S.Raw)‖
  rw [_root_.DirectLimit.normedAddCommGroupOfNormPreserving_norm_mk S.map S.norm_map]
  exact NonUnitalStarAlgHom.norm_apply_le (g i) a

/-- **Continuous linear universal limit map.** The compatible C-star stage maps induce the
continuous complex-linear map on `S.Raw` with values `[i,x] ↦ g_i(x)` and norm bound one. -/
def rawLiftCLM : S.Raw →L[ℂ] C :=
  (LinearMap.ofClass (S.rawLift g hg)).mkContinuous 1 fun x => by
    simpa only [one_mul, LinearMap.coe_ofClass] using S.norm_rawLift_le g hg x

/-- **Universal map on the completed limit.** For a nonempty directed isometric C-star system and
compatible star maps `g_i : S.Stage i → C`, extend the contractive algebraic limit map to
`S.Completed → C`. -/
def lift : S.Completed →⋆ₙₐ[ℂ] C := by
  let L := rawLiftCLM S g hg
  let F : S.Completed → C := UniformSpace.Completion.extension L
  have hF : Continuous F := UniformSpace.Completion.continuous_extension
  have hcoe (a : S.Raw) : F (a : S.Completed) = S.rawLift g hg a := by
    exact UniformSpace.Completion.extension_coe L.uniformContinuous a
  exact
    { toFun := F
      map_zero' := by
        rw [← UniformSpace.Completion.coe_zero, hcoe, map_zero]
      map_add' := by
        intro x y
        refine UniformSpace.Completion.induction_on₂ x y
          (isClosed_eq (hF.comp (continuous_fst.add continuous_snd))
            ((hF.comp continuous_fst).add (hF.comp continuous_snd))) ?_
        intro a b
        rw [← UniformSpace.Completion.coe_add, hcoe, hcoe, hcoe, map_add]
      map_mul' := by
        intro x y
        refine UniformSpace.Completion.induction_on₂ x y
          (isClosed_eq (hF.comp (continuous_fst.mul continuous_snd))
            ((hF.comp continuous_fst).mul (hF.comp continuous_snd))) ?_
        intro a b
        rw [← UniformSpace.Completion.nonUnitalCompletion_coe_mul S.Raw,
          hcoe, hcoe, hcoe, map_mul]
      map_smul' := by
        intro c x
        refine UniformSpace.Completion.induction_on x
          (isClosed_eq (hF.comp (continuous_const_smul c)) (hF.const_smul c)) ?_
        intro a
        simp only [← UniformSpace.Completion.coe_smul, hcoe, map_smul, MonoidHom.coe_id, id]
      map_star' := by
        intro x
        refine UniformSpace.Completion.induction_on x
          (isClosed_eq (hF.comp continuous_star) (continuous_star.comp hF)) ?_
        intro a
        rw [CStarAlgebra.completionNonUnitalCStarAlgebra_star_coe S.Raw,
          hcoe, hcoe, map_star] }

@[simp]
theorem lift_coe (a : S.Raw) : S.lift g hg (a : S.Completed) = S.rawLift g hg a := by
  exact UniformSpace.Completion.extension_coe (rawLiftCLM S g hg).uniformContinuous a

/-- **Universal map on a stage image.** For compatible stage maps, `S.lift g hg (S.of i x) = g i
x`. -/
@[simp]
theorem lift_of (i : I) (x : S.Stage i) : S.lift g hg (S.of i x) = g i x := by
  change S.lift g hg (S.rawOf i x : S.Completed) = g i x
  rw [S.lift_coe g hg, S.rawLift_rawOf g hg]

/-- **Uniqueness of the completed universal map.** A complex nonunital star homomorphism `H :
S.Completed → C` agreeing with `g_i` on every stage inclusion equals `S.lift g hg`. -/
theorem lift_unique (H : S.Completed →⋆ₙₐ[ℂ] C)
    (hH : ∀ i, H.comp (S.of i) = g i) : H = S.lift g hg := by
  apply NonUnitalStarAlgHom.ext
  intro x
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (map_continuous H) (map_continuous (S.lift g hg))) ?_
  intro a
  refine _root_.DirectLimit.induction (f := S.map) (fun i z => ?_) a
  change H (S.of i z) = S.lift g hg (S.of i z)
  calc
    H (S.of i z) = g i z := by
      simpa only [NonUnitalStarAlgHom.comp_apply] using DFunLike.congr_fun (hH i) z
    _ = S.lift g hg (S.of i z) := (S.lift_of g hg i z).symm

include hg in
/-- **C-star universal property of the completed limit.** Compatible complex nonunital star maps
`g_i : S.Stage i → C` into a nonunital C-star algebra determine exactly one star homomorphism
`H : S.Completed → C` with `H.comp (S.of i) = g_i`. -/
theorem universal : ∃! H : S.Completed →⋆ₙₐ[ℂ] C, ∀ i, H.comp (S.of i) = g i := by
  refine ⟨S.lift g hg, ?_, fun H hH => S.lift_unique g hg H hH⟩
  intro i
  ext x
  exact S.lift_of g hg i x

/-- **Isometric universal limit map.** If compatible stage maps `g_i` preserve every stage norm,
then `‖S.lift g hg x‖ = ‖x‖` for all completed limit elements `x`. -/
theorem norm_lift_of_norm_preserving
    (hgnorm : ∀ i (x : S.Stage i), ‖g i x‖ = ‖x‖) (x : S.Completed) :
    ‖S.lift g hg x‖ = ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (map_continuous (S.lift g hg)).norm continuous_norm) ?_
  intro a
  refine _root_.DirectLimit.induction (f := S.map) (fun i z => ?_) a
  change ‖S.lift g hg (S.of i z)‖ = ‖S.of i z‖
  rw [S.lift_of g hg, S.norm_of]
  exact hgnorm i z

/-- **Injectivity from stage norm preservation.** If the compatible maps `g_i` preserve norms on
each stage, their completed universal map `S.lift g hg` is injective. -/
theorem lift_injective_of_norm_preserving
    (hgnorm : ∀ i (x : S.Stage i), ‖g i x‖ = ‖x‖) :
    Function.Injective (S.lift g hg) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [← S.norm_lift_of_norm_preserving g hg hgnorm (x - y),
    map_sub, hxy, sub_self, norm_zero]

/-- **Surjectivity of a faithful dense limit map.** If `S.lift g hg` is injective and the union `⋃
i, Set.range (g i)` is dense in the target C-star algebra `C`, the completed universal map is
surjective. -/
theorem lift_surjective_of_dense_range
    (hinj : Function.Injective (S.lift g hg))
    (hdense : Dense (⋃ i, Set.range (g i))) : Function.Surjective (S.lift g hg) := by
  have hclosed : IsClosed (Set.range (S.lift g hg)) :=
    (NonUnitalStarAlgHom.isometry (S.lift g hg) hinj).isClosedEmbedding.isClosed_range
  have hsubset : (⋃ i, Set.range (g i)) ⊆ Set.range (S.lift g hg) := by
    intro a ha
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
    obtain ⟨x, rfl⟩ := hi
    exact ⟨S.of i x, S.lift_of g hg i x⟩
  have hrange : Set.range (S.lift g hg) = Set.univ := by
    rw [← hclosed.closure_eq]
    exact (hdense.mono hsubset).closure_eq
  exact Set.range_eq_univ.mp hrange

end Universal

end IsometricSystem

end CStarAlgebra.DirectLimit
