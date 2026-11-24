/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexW
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidAction
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationWeakEquivalence

/-!
# Cancellation for simplicial weak equivalences

Precomposition cancellation for KanComplex.W follows by cancelling homotopy-group maps at
vertices in the image and transporting to arbitrary basepoints through the fundamental
groupoid. Together with the other composition laws, it gives W.precomp_iff and the
two-out-of-three instance. The file also proves that a lies in W whenever a ≫ b and b ≫ c
do, and transports this implication to realization weak equivalences.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SSet

namespace KanComplex

-- The precomposition proof uses the fundamental-groupoid action to transport
-- homotopy-group bijectivity from image points to arbitrary basepoints.

private lemma mapFundamentalGroupoid_comp' {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    SSet.mapFundamentalGroupoid (f ≫ g) =
      SSet.mapFundamentalGroupoid f ⋙ SSet.mapFundamentalGroupoid g := by
  unfold SSet.mapFundamentalGroupoid
  have h1 : (truncation (2 : ℕ)).map (f ≫ g) =
      (truncation (2 : ℕ)).map f ≫ (truncation (2 : ℕ)).map g := by simp
  rw [h1]
  exact SSet.Truncated.mapFundamentalGroupoid_comp ((truncation (2 : ℕ)).map f)
    ((truncation (2 : ℕ)).map g)

/-- Bijectivity of the homotopy-group map for an isomorphism. -/
theorem W.bijective_of_iso {X Y : SSet.{u}} (e : X ≅ Y) [KanComplex X] [KanComplex Y]
    {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : e.hom.app _ x = y) (n : ℕ) :
    Function.Bijective (KanComplex.π.map e.hom h (n := n)) :=
  (KanComplex.π.equivOfIso e h n).bijective

/-- Right cancellation: if `f` and `f ≫ g` are weak equivalences, so is `g`. -/
theorem W.of_precomp {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : W f) (hfg : W (f ≫ g)) : W g := by
  obtain ⟨hX, hY, hEquivF, hBijF⟩ := hf
  obtain ⟨_, hZ, hEquivFG, hBijFG⟩ := hfg
  refine ⟨hY, hZ, ?_, ?_⟩
  · have h_comp : SSet.mapFundamentalGroupoid (f ≫ g) =
        SSet.mapFundamentalGroupoid f ⋙ SSet.mapFundamentalGroupoid g :=
      mapFundamentalGroupoid_comp' f g
    have hF : (SSet.mapFundamentalGroupoid f).IsEquivalence := hEquivF
    have hFG : (SSet.mapFundamentalGroupoid (f ≫ g)).IsEquivalence := hEquivFG
    rw [h_comp] at hFG
    exact Functor.isEquivalence_of_comp_left (SSet.mapFundamentalGroupoid f)
      (SSet.mapFundamentalGroupoid g)
  · intro n y
    -- Step 1: bijectivity at points in the image of f
    have hBijF_at : ∀ (x : X _⦋0⦌), Function.Bijective
        (KanComplex.π.map g (rfl : g.app _ (f.app _ x) = g.app _ (f.app _ x)) (n := n)) := by
      intro x
      have hBijF_n := hBijF n x
      have hBijFG_n := hBijFG n x
      have h_eq : KanComplex.π.map (f ≫ g) (rfl : (f ≫ g).app _ x = (f ≫ g).app _ x) (n := n) =
          (KanComplex.π.map g (rfl : g.app _ (f.app _ x) = g.app _ (f.app _ x)) (n := n)) ∘
            (KanComplex.π.map f (rfl : f.app _ x = f.app _ x) (n := n)) := by
        funext q
        have h1 := KanComplex.π.map_comp (f := f) (g := g)
          (hx := (rfl : f.app _ x = f.app _ x))
          (hy := (rfl : g.app _ (f.app _ x) = g.app _ (f.app _ x)))
          (n := n) (x := x) q
        simp only at h1
        exact h1
      have hBijComp : Function.Bijective
          ((KanComplex.π.map g (rfl : g.app _ (f.app _ x) = g.app _ (f.app _ x)) (n := n)) ∘
            (KanComplex.π.map f (rfl : f.app _ x = f.app _ x) (n := n))) := by
        rw [← h_eq]
        exact hBijFG_n
      exact (Function.Bijective.of_comp_iff
        (KanComplex.π.map g (rfl : g.app _ (f.app _ x) = g.app _ (f.app _ x)) (n := n))
        hBijF_n).mp hBijComp
    -- Step 2: transport to arbitrary y via essential surjectivity and action
    -- Obtain x and iso mk (f x) ≅ mk y
    have hExists :
        ∃ (x : X _⦋0⦌) (p : SSet.FundamentalGroupoid.mk (f.app _ x) ⟶
          SSet.FundamentalGroupoid.mk y),
        True := by
      -- Use EssSurj to get an object iso, then extract witness via mk surjectivity
      let yFG : SSet.FundamentalGroupoid Y := SSet.FundamentalGroupoid.mk y
      obtain ⟨xFG, ⟨isoFG : (SSet.mapFundamentalGroupoid f).obj xFG ≅ yFG⟩⟩ :=
        Functor.EssSurj.mem_essImage (SSet.mapFundamentalGroupoid f) yFG
      obtain ⟨x, rfl⟩ : ∃ (x : X _⦋0⦌), xFG = SSet.FundamentalGroupoid.mk x := by
        exact ⟨(SSet.FundamentalGroupoid.mk_surjective xFG).choose,
          (SSet.FundamentalGroupoid.mk_surjective xFG).choose_spec.symm⟩
      have hObj : (SSet.mapFundamentalGroupoid f).obj (SSet.FundamentalGroupoid.mk x) =
          SSet.FundamentalGroupoid.mk (f.app _ x) := by
        simp [SSet.mapFundamentalGroupoid_obj_mk]
      -- transport iso along equality
      let iso' : SSet.FundamentalGroupoid.mk (f.app _ x) ≅ yFG :=
        (eqToIso hObj).trans isoFG
      exact ⟨x, iso'.hom, trivial⟩
    obtain ⟨x, p, _⟩ := hExists
    -- action witnesses
    have hActionFX : Function.Bijective
        (KanComplex.π.map g (rfl : g.app _ (f.app _ x) = g.app _ (f.app _ x)) (n := n)) :=
      hBijF_at x
    have hActionY : Function.Bijective (KanComplex.π.action (n := n) p) :=
      KanComplex.π.action_bijective p
    have hActionMap : Function.Bijective
        (KanComplex.π.action (n := n) ((SSet.mapFundamentalGroupoid g).map p)) :=
      KanComplex.π.action_bijective ((SSet.mapFundamentalGroupoid g).map p)
    -- Naturality square: g-action
    have hNat : ∀ (q : KanComplex.π n Y (f.app _ x)),
        KanComplex.π.map g rfl n (KanComplex.π.action (n := n) p q) =
          KanComplex.π.action (n := n) ((SSet.mapFundamentalGroupoid g).map p)
            (KanComplex.π.map g rfl n q) := by
      intro q
      exact KanComplex.π.action_naturality g p q
    -- deduce bijectivity of π.map g at y from the square
    have hEq : (KanComplex.π.map g rfl n ∘ KanComplex.π.action (n := n) p) =
        (KanComplex.π.action (n := n) ((SSet.mapFundamentalGroupoid g).map p) ∘
          KanComplex.π.map g (rfl : g.app _ (f.app _ x) = g.app _ (f.app _ x)) n) := by
      funext q
      exact hNat q
    have hBijCompRight : Function.Bijective
        (KanComplex.π.action (n := n) ((SSet.mapFundamentalGroupoid g).map p) ∘
          KanComplex.π.map g (rfl : g.app _ (f.app _ x) = g.app _ (f.app _ x)) n) :=
      Function.Bijective.comp hActionMap hActionFX
    have hBijCompLeft : Function.Bijective
        (KanComplex.π.map g (rfl : g.app _ y = g.app _ y) n ∘ KanComplex.π.action (n := n) p) := by
      rw [hEq]
      exact hBijCompRight
    exact (Function.Bijective.of_comp_iff
      (KanComplex.π.map g (rfl : g.app _ y = g.app _ y) n)
      hActionY).mp hBijCompLeft

/-- If `W f` then `W (f ≫ g) ↔ W g`. -/
theorem W.precomp_iff {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : W f) : W (f ≫ g) ↔ W g :=
  ⟨fun hfg => W.of_precomp hf hfg, fun hg => W.comp hf hg⟩

instance W.hasOfPrecompProperty : W.HasOfPrecompProperty W where
  of_precomp _ _ hf hfg := W.of_precomp hf hfg

instance W.hasTwoOutOfThreeProperty : W.HasTwoOutOfThreeProperty where
  comp_mem _ _ hf hg := W.comp hf hg
  of_postcomp _ _ hg hfg := W.of_postcomp hg hfg
  of_precomp _ _ hf hfg := W.of_precomp hf hfg

/-- The middle functor of a chain of three functors whose two
consecutive composites are equivalences is an equivalence. The
inverse functor is assembled from the two one-sided inverses
(`H ⋙ Q` is a right inverse of `G` up to isomorphism, `P ⋙ F` a
left inverse, and they are isomorphic by the usual
`L ≅ L ⋙ (G ⋙ R) ≅ R` argument). This is the category-level
two-out-of-six step used for fundamental groupoids below. -/
private theorem isEquivalence_of_comp_comp_middle
    {C D E K : Type*} [Category* C] [Category* D] [Category* E]
    [Category* K] (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ K)
    [Functor.IsEquivalence (F ⋙ G)] [Functor.IsEquivalence (G ⋙ H)] :
    Functor.IsEquivalence G := by
  let P := (F ⋙ G).asEquivalence.inverse
  let Q := (G ⋙ H).asEquivalence.inverse
  have hGR : G ⋙ (H ⋙ Q) ≅ 𝟭 D :=
    (G ⋙ H).asEquivalence.unitIso.symm
  have hLG : (P ⋙ F) ⋙ G ≅ 𝟭 E :=
    (F ⋙ G).asEquivalence.counitIso
  have hLR : P ⋙ F ≅ H ⋙ Q :=
    (Functor.isoWhiskerLeft (P ⋙ F) hGR.symm) ≪≫
      (Functor.isoWhiskerRight hLG (H ⋙ Q))
  have hRG : (H ⋙ Q) ⋙ G ≅ 𝟭 E :=
    (Functor.isoWhiskerRight hLR.symm G) ≪≫ hLG
  exact Functor.IsEquivalence.mk' (H ⋙ Q) hGR.symm hRG

/-- **Two-out-of-six for `SSet.KanComplex.W`, left map**: if
`a ≫ b` and `b ≫ c` are weak equivalences between Kan complexes
then so is `a`. This does not follow from abstract two-out-of-three
for `W` (`SSet.KanComplex.W.hasTwoOutOfThreeProperty`); it is
proved from the defining invariants: equivalences of categories
satisfy two-out-of-six (`isEquivalence_of_comp_comp_middle` plus
cancellation), and for the based homotopy-group maps at a vertex
`x` of `A`, the two composite bijections force the middle map at
`a.app _ x` to be bijective (injective from the second composite,
surjective from the first), hence the first map is bijective. The
analogous statements for the middle and right maps at *arbitrary*
basepoints would additionally need basepoint transport along the
fundamental groupoid (as in `SSet.KanComplex.W.of_precomp`) and
are not needed here. -/
theorem W.left_of_comp_comp {A B C D : SSet.{u}}
    {a : A ⟶ B} {b : B ⟶ C} {c : C ⟶ D}
    (hab : KanComplex.W (a ≫ b)) (hbc : KanComplex.W (b ≫ c)) :
    KanComplex.W a := by
  obtain ⟨hA, _hC, hFGab, hπab⟩ := hab
  obtain ⟨hB, _hD, hFGbc, hπbc⟩ := hbc
  refine ⟨hA, hB, ?_, ?_⟩
  · have habFG : (SSet.mapFundamentalGroupoid a ⋙
        SSet.mapFundamentalGroupoid b).IsEquivalence := by
      rw [← mapFundamentalGroupoid_comp']
      exact hFGab
    have hbcFG : (SSet.mapFundamentalGroupoid b ⋙
        SSet.mapFundamentalGroupoid c).IsEquivalence := by
      rw [← mapFundamentalGroupoid_comp']
      exact hFGbc
    have : (SSet.mapFundamentalGroupoid a ⋙
        SSet.mapFundamentalGroupoid b).IsEquivalence := habFG
    have : (SSet.mapFundamentalGroupoid b ⋙
        SSet.mapFundamentalGroupoid c).IsEquivalence := hbcFG
    have : (SSet.mapFundamentalGroupoid b).IsEquivalence :=
      isEquivalence_of_comp_comp_middle (SSet.mapFundamentalGroupoid a)
        (SSet.mapFundamentalGroupoid b) (SSet.mapFundamentalGroupoid c)
    exact Functor.isEquivalence_of_comp_right
      (SSet.mapFundamentalGroupoid a) (SSet.mapFundamentalGroupoid b)
  · intro n x
    have hEq1 : KanComplex.π.map (a ≫ b)
        (rfl : (a ≫ b).app _ x = (a ≫ b).app _ x) (n := n) =
        (KanComplex.π.map b
          (rfl : b.app _ (a.app _ x) = b.app _ (a.app _ x)) (n := n)) ∘
          (KanComplex.π.map a (rfl : a.app _ x = a.app _ x) (n := n)) := by
      funext q
      have h1 := KanComplex.π.map_comp (f := a) (g := b) (hx := rfl)
        (hy := rfl) (n := n) (x := x) q
      simp only at h1
      exact h1
    have hEq2 : KanComplex.π.map (b ≫ c)
        (rfl : (b ≫ c).app _ (a.app _ x) = (b ≫ c).app _ (a.app _ x))
        (n := n) =
        (KanComplex.π.map c
          (rfl : c.app _ (b.app _ (a.app _ x)) =
            c.app _ (b.app _ (a.app _ x))) (n := n)) ∘
          (KanComplex.π.map b
            (rfl : b.app _ (a.app _ x) = b.app _ (a.app _ x))
            (n := n)) := by
      funext q
      have h1 := KanComplex.π.map_comp (f := b) (g := c) (hx := rfl)
        (hy := rfl) (n := n) (x := a.app _ x) q
      simp only at h1
      exact h1
    have hBij1 : Function.Bijective
        ((KanComplex.π.map b
            (rfl : b.app _ (a.app _ x) = b.app _ (a.app _ x))
            (n := n)) ∘
          (KanComplex.π.map a (rfl : a.app _ x = a.app _ x)
            (n := n))) := by
      rw [← hEq1]
      exact hπab n x
    have hBij2 : Function.Bijective
        ((KanComplex.π.map c
            (rfl : c.app _ (b.app _ (a.app _ x)) =
              c.app _ (b.app _ (a.app _ x))) (n := n)) ∘
          (KanComplex.π.map b
            (rfl : b.app _ (a.app _ x) = b.app _ (a.app _ x))
            (n := n))) := by
      rw [← hEq2]
      exact hπbc n (a.app _ x)
    have hψ : Function.Bijective (KanComplex.π.map b
        (rfl : b.app _ (a.app _ x) = b.app _ (a.app _ x)) (n := n)) :=
      ⟨Function.Injective.of_comp hBij2.injective,
        Function.Surjective.of_comp hBij1.surjective⟩
    exact (Function.Bijective.of_comp_iff' hψ _).mp hBij1

end KanComplex

/-- **Two-out-of-six for `SSet.realizationWeakEquivalences`, left
map**: transported from `SSet.KanComplex.W.left_of_comp_comp`
along realization–singularization, whose values are Kan
complexes. -/
theorem realizationWeakEquivalences.left_of_comp_comp {A B C D : SSet.{u}}
    {a : A ⟶ B} {b : B ⟶ C} {c : C ⟶ D}
    (hab : realizationWeakEquivalences (a ≫ b))
    (hbc : realizationWeakEquivalences (b ≫ c)) :
    realizationWeakEquivalences a := by
  have h1 : KanComplex.W
      ((SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).map a ≫
        (SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).map b) := by
    rw [← Functor.map_comp]
    exact hab
  have h2 : KanComplex.W
      ((SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).map b ≫
        (SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).map c) := by
    rw [← Functor.map_comp]
    exact hbc
  exact KanComplex.W.left_of_comp_comp h1 h2

end SSet
