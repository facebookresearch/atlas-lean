/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.QMIsogeny

/-!
# Tests for isogenies, lattice actions and representability of fake elliptic curves
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

open scoped Quaternion

universe u

namespace QMIsogenyTest

open CerednikDrinfeld.QM

variable {a b : ℚ} {Λ : Subring ℍ[ℚ, a, b]} {N : ℕ}

/-- Consumer with the original binders for isogeny pairs. -/
private theorem exactSource {S : Type u} [CommRing S] (d : ℕ)
    (E E' : FakeEllipticCurve Λ N S) (φ : E.A ⟶ E'.A) (ψ : E'.A ⟶ E.A) :
    FakeEllipticCurve.IsIsogenyPair d E E' φ ψ ↔
      ∃ (hφ : φ ≫ E'.f = E.f) (hψ : ψ ≫ E.f = E'.f),
        FakeEllipticCurve.IsIsogenyPairVia d E E' φ hφ ψ hψ :=
  FakeEllipticCurve.isIsogenyPair_iff_exists_via d E E' φ ψ

/-- The integer of an isogeny pair is positive: no fake elliptic curve is
`0`-isogenous to another. -/
example {S : Type u} [CommRing S] (E E' : FakeEllipticCurve Λ N S) :
    ¬ FakeEllipticCurve.IsIsogeny 0 E E' := by
  rintro ⟨φ, ψ, hd, _⟩
  exact lt_irrefl 0 hd

/-- The composites of an isogeny pair are the action of the element `d` of
`Λ`, with no membership hypothesis: the identity pair is a `d`-isogeny pair
of `E` with itself exactly when `d` is positive and acts as the identity. -/
example {S : Type u} [CommRing S] (d : ℕ) (E : FakeEllipticCurve Λ N S) :
    FakeEllipticCurve.IsIsogenyPair d E E (𝟙 E.A) (𝟙 E.A) ↔
      0 < d ∧ E.act (d : ↥Λ) = 𝟙 E.A := by
  constructor
  · rintro ⟨hd, _, _, _, _, _, _, hc, _⟩
    exact ⟨hd, by rw [← hc, Category.comp_id]⟩
  · rintro ⟨hd, h1⟩
    refine ⟨hd, Category.comp_id E.f, Category.comp_id E.f, ?_, ?_, ?_, ?_, ?_⟩
    · intro T t P Q
      rw [FakeEllipticCurve.mapPt_id, FakeEllipticCurve.mapPt_id,
        FakeEllipticCurve.mapPt_id]
    · intro T t P Q
      rw [FakeEllipticCurve.mapPt_id, FakeEllipticCurve.mapPt_id,
        FakeEllipticCurve.mapPt_id]
    · intro x
      rw [Category.id_comp, Category.comp_id]
    · intro x
      rw [Category.id_comp, Category.comp_id]
    · rw [h1]
      exact ⟨Category.comp_id _, Category.comp_id _⟩

/-- The composites satisfy the source's equations for every proof that the
rational scalar `d` lies in `Λ`: the element `d` of `Λ` is that scalar. -/
example {S : Type u} [CommRing S] {d : ℕ} {E E' : FakeEllipticCurve Λ N S}
    {φ : E.A ⟶ E'.A} {ψ : E'.A ⟶ E.A}
    (h : FakeEllipticCurve.IsIsogenyPair d E E' φ ψ)
    (hd : ((d : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) :
    φ ≫ ψ = E.act ⟨((d : ℚ) : ℍ[ℚ, a, b]), hd⟩ ∧
      ψ ≫ φ = E'.act ⟨((d : ℚ) : ℍ[ℚ, a, b]), hd⟩ := by
  have hΛ : (⟨((d : ℚ) : ℍ[ℚ, a, b]), hd⟩ : ↥Λ) = (d : ↥Λ) :=
    Subtype.ext (by norm_cast)
  obtain ⟨_, _, _, _, _, _, _, hc⟩ := h
  rw [hΛ]
  exact hc

/-- Every fake elliptic curve is `1`-isogenous to itself, and isogeny is
symmetric. -/
example {S : Type u} [CommRing S] (E E' : FakeEllipticCurve Λ N S)
    (h : FakeEllipticCurve.IsIsogeny 3 E E') :
    FakeEllipticCurve.IsIsogeny 1 E E ∧ FakeEllipticCurve.IsIsogeny 3 E' E :=
  ⟨FakeEllipticCurve.isIsogeny_one_refl E, h.symm⟩

/-- The lattice action of a fake elliptic curve is its action of `Λ`, and it
is unital and multiplicative with no membership hypothesis. -/
example {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ N S) (x y : ↥Λ) :
    (LatticeAction.ofFakeEllipticCurve E).act = E.act ∧
      (LatticeAction.ofFakeEllipticCurve E).act 1 = 𝟙 E.A ∧
      (LatticeAction.ofFakeEllipticCurve E).act (x * y) =
        E.act y ≫ E.act x :=
  ⟨LatticeAction.ofFakeEllipticCurve_act E,
    (LatticeAction.ofFakeEllipticCurve E).act_one,
    (LatticeAction.ofFakeEllipticCurve E).act_mul x y⟩

/-- `ofFakeEllipticCurve_act` is a simp lemma, and lattice actions are equal
when their actions are: for the lattice action of a fake elliptic curve `E`,
the generated `LatticeAction.ext_iff` compares with `E.act`. -/
example {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ N S)
    (X : LatticeAction Λ E.f E.L) :
    (LatticeAction.ofFakeEllipticCurve E).act = E.act ∧
      (LatticeAction.ofFakeEllipticCurve E = X ↔ E.act = X.act) :=
  ⟨by simp, LatticeAction.ext_iff⟩

/-- A point of `Spec R` over itself is determined by its test scheme map. -/
private theorem point_ext {R : Type u} [CommRing R] {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)}
    (x y : SchemeHomOver t (𝟙 (Spec (CommRingCat.of R)))) : x = y :=
  Over.OverMorphism.ext (by simpa using (Over.w x).trans (Over.w y).symm)

/-- The trivial relative group law on `Spec R` over itself. -/
private def trivialLaw (R : Type u) [CommRing R] :
    RelativeGroupLaw R (𝟙 (Spec (CommRingCat.of R))) where
  mul _ x _ := x
  one t := Over.homMk t (Category.comp_id t)
  inv _ x := x
  mul_assoc _ _ _ _ := rfl
  one_mul _ _ := point_ext _ _
  mul_one _ _ := rfl
  inv_mul_cancel _ _ := point_ext _ _
  mul_natural _ _ _ _ _ _ := rfl

/-- Every subring `Λ` acts on the trivial group law by identities, so lattice
actions with the unital and multiplicative conditions exist. -/
example (R : Type u) [CommRing R] :
    Nonempty (LatticeAction Λ (𝟙 (Spec (CommRingCat.of R))) (trivialLaw R)) :=
  ⟨{ act := fun _ => 𝟙 _
     act_over := fun _ => Category.id_comp _
     act_hom := fun _ _ _ _ _ => point_ext _ _
     act_one := rfl
     act_mul := fun _ _ => (Category.comp_id _).symm
     act_add := fun _ _ _ _ _ => point_ext _ _ }⟩

/-- The action of an element of `Λ` preserves the level structure, since
level points are stable under `Λ`. -/
example {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ N S) (x : ↥Λ) :
    FakeEllipticCurve.PreservesLevel E E (E.act x) (E.act_over x) :=
  fun t P hP => E.lev_stable x t P hP

/-- A pullback of fake elliptic curves is a pullback of their group laws. -/
private theorem isGroupPullback_of_isPullbackVia {S S' : Type u} [CommRing S]
    [CommRing S'] {φ : S →+* S'} {E : FakeEllipticCurve Λ N S}
    {E' : FakeEllipticCurve Λ N S'} {g : E'.A ⟶ E.A}
    (h : FakeEllipticCurve.IsPullbackVia φ E E' g) :
    IsGroupPullback φ E.L E'.L g := by
  obtain ⟨hg, hmul, -, -⟩ := h
  exact ⟨hg, hmul⟩

section LatticeActionRepresentability

variable {R : Type u} [CommRing R] {A : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} {L : RelativeGroupLaw R f}
  {M : Scheme.{u}} {πM : M ⟶ Spec (CommRingCat.of R)}
  {cl : ∀ (R' : Type u) [CommRing R'] (φ : R →+* R') {A' : Scheme.{u}}
    {f' : A' ⟶ Spec (CommRingCat.of R')} (L' : RelativeGroupLaw R' f')
    (g : A' ⟶ A), IsGroupPullback φ L L' g → LatticeAction Λ f' L' →
    SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πM}

/-- Over a fixed pullback of `L`, each point of a representing scheme comes
from exactly one lattice action. -/
example (h : RepresentsLatticeActions Λ L M πM cl) (R' : Type u)
    [CommRing R'] (φ : R →+* R') {A' : Scheme.{u}}
    {f' : A' ⟶ Spec (CommRingCat.of R')} (L' : RelativeGroupLaw R' f')
    (g : A' ⟶ A) (hg : IsGroupPullback φ L L' g)
    (s : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πM) :
    ∃! X' : LatticeAction Λ f' L', cl R' φ L' g hg X' = s :=
  (h.cl_bijective R' φ L' g hg).existsUnique s

/-- Representability determines transported actions: on a pullback along
`ψ` via `k`, two lattice actions that `k` intertwines with the same action
`X'` have the same point, so they are equal. -/
example (h : RepresentsLatticeActions Λ L M πM cl) (R' : Type u)
    [CommRing R'] (φ : R →+* R') {A' : Scheme.{u}}
    {f' : A' ⟶ Spec (CommRingCat.of R')} (L' : RelativeGroupLaw R' f')
    (g : A' ⟶ A) (hg : IsGroupPullback φ L L' g) (X' : LatticeAction Λ f' L')
    (R'' : Type u) [CommRing R''] (ψ : R' →+* R'') {A'' : Scheme.{u}}
    {f'' : A'' ⟶ Spec (CommRingCat.of R'')} (L'' : RelativeGroupLaw R'' f'')
    (g'' : A'' ⟶ A) (hg'' : IsGroupPullback (ψ.comp φ) L L'' g'')
    (k : A'' ⟶ A') (hk : IsGroupPullback ψ L' L'' k) (hkg : k ≫ g = g'')
    (X₁ X₂ : LatticeAction Λ f'' L'')
    (h₁ : ∀ x : ↥Λ, X₁.act x ≫ k = k ≫ X'.act x)
    (h₂ : ∀ x : ↥Λ, X₂.act x ≫ k = k ≫ X'.act x) : X₁ = X₂ := by
  apply (h.cl_bijective R'' (ψ.comp φ) L'' g'' hg'').injective
  apply Over.OverMorphism.ext
  rw [h.cl_comp R' φ L' g hg X' R'' ψ L'' g'' hg'' X₁ k hk hkg h₁,
    h.cl_comp R' φ L' g hg X' R'' ψ L'' g'' hg'' X₂ k hk hkg h₂]

end LatticeActionRepresentability

/-- Base change of fake elliptic curves: if `E₁` and `E₂` are pullbacks of
`E₀` and `E₂` is the pullback of `E₁` along `ψ` via a map `k` compatible with
their maps to `E₀`, the point of the action of `E₂` is the base change along
`ψ` of the point of the action of `E₁`. The pullback structure of `k` gives
the intertwining of the two actions that naturality asks for. -/
example {R : Type u} [CommRing R] (E₀ : FakeEllipticCurve Λ N R)
    {M : Scheme.{u}} {πM : M ⟶ Spec (CommRingCat.of R)}
    {cl : ∀ (R' : Type u) [CommRing R'] (φ : R →+* R') {A' : Scheme.{u}}
      {f' : A' ⟶ Spec (CommRingCat.of R')} (L' : RelativeGroupLaw R' f')
      (g : A' ⟶ E₀.A), IsGroupPullback φ E₀.L L' g →
      LatticeAction Λ f' L' → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πM}
    (h : RepresentsLatticeActions Λ E₀.L M πM cl) {R' : Type u}
    [CommRing R'] (φ : R →+* R') (E₁ : FakeEllipticCurve Λ N R')
    (g₁ : E₁.A ⟶ E₀.A) (h₁ : FakeEllipticCurve.IsPullbackVia φ E₀ E₁ g₁)
    {R'' : Type u} [CommRing R''] (ψ : R' →+* R'')
    (E₂ : FakeEllipticCurve Λ N R'') (g₂ : E₂.A ⟶ E₀.A)
    (h₂ : FakeEllipticCurve.IsPullbackVia (ψ.comp φ) E₀ E₂ g₂)
    (k : E₂.A ⟶ E₁.A) (hk : FakeEllipticCurve.IsPullbackVia ψ E₁ E₂ k)
    (hkg : k ≫ g₁ = g₂) :
    (cl R'' (ψ.comp φ) E₂.L g₂ (isGroupPullback_of_isPullbackVia h₂)
        (LatticeAction.ofFakeEllipticCurve E₂)).left =
      Spec.map (CommRingCat.ofHom ψ) ≫
        (cl R' φ E₁.L g₁ (isGroupPullback_of_isPullbackVia h₁)
          (LatticeAction.ofFakeEllipticCurve E₁)).left := by
  have hact : ∀ x : ↥Λ, (LatticeAction.ofFakeEllipticCurve E₂).act x ≫ k =
      k ≫ (LatticeAction.ofFakeEllipticCurve E₁).act x := by
    obtain ⟨-, -, hact, -⟩ := hk
    exact hact
  exact h.cl_comp R' φ E₁.L g₁ (isGroupPullback_of_isPullbackVia h₁)
    (LatticeAction.ofFakeEllipticCurve E₁) R'' ψ E₂.L g₂
    (isGroupPullback_of_isPullbackVia h₂)
    (LatticeAction.ofFakeEllipticCurve E₂) k
    (isGroupPullback_of_isPullbackVia hk) hkg hact

/-- `RepresentsOn` is the four-part characterization: invariance under
isomorphisms of the pullbacks, compatible with their maps to `E` and `A`,
that carry both maps of one pair to both maps of the other, naturality in the
base ring, surjectivity, and faithfulness on both maps. -/
private theorem exactSourceRepresents {S : Type} [CommRing S] (r d : ℕ)
    (E A : FakeEllipticCurve Λ N S) {X : Scheme.{0}}
    (ξ : X ⟶ Spec (CommRingCat.of S))
    (pt : FakeEllipticCurve.IsogenyPair.PtFamily r d E A ξ) :
    FakeEllipticCurve.IsogenyPair.RepresentsOn r d E A ξ pt ↔
      (∀ (T : Type) [CommRing T] [Algebra S T]
        (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A)
        (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
        (gA : A'.A ⟶ A.A)
        (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
        (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
        (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ')
        (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ)
        (E'' A'' : FakeEllipticCurve Λ N T) (gE'' : E''.A ⟶ E.A)
        (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E''
          gE'')
        (gA'' : A''.A ⟶ A.A)
        (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A''
          gA'')
        (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hψ : ψ ≫ A''.f = E''.f)
        (hq : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' ψ ψ')
        (hm : FakeEllipticCurve.PreservesLevel E'' A'' ψ hψ)
        (iE : E'.A ≅ E''.A) (hiE : iE.hom ≫ E''.f = E'.f)
        (iA : A'.A ≅ A''.A) (hiA : iA.hom ≫ A''.f = A'.f),
        FakeEllipticCurve.IsoVia E' E'' iE hiE →
        FakeEllipticCurve.IsoVia A' A'' iA hiA → iE.hom ≫ gE'' = gE →
        iA.hom ≫ gA'' = gA → iE.hom ≫ ψ = φ ≫ iA.hom →
        iA.hom ≫ ψ' = φ' ≫ iE.hom →
        pt T E' A' gE hgE gA hgA φ φ' hφ hp hl =
          pt T E'' A'' gE'' hgE'' gA'' hgA'' ψ ψ' hψ hq hm) ∧
      (∀ (T T' : Type) [CommRing T] [Algebra S T] [CommRing T']
        [Algebra S T'] (f : T →ₐ[S] T')
        (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A)
        (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
        (gA : A'.A ⟶ A.A)
        (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
        (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
        (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ')
        (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ)
        (E'' A'' : FakeEllipticCurve Λ N T') (hE : E''.A ⟶ E'.A)
        (_hhE : FakeEllipticCurve.IsPullbackVia (f : T →+* T') E' E'' hE)
        (hA : A''.A ⟶ A'.A)
        (_hhA : FakeEllipticCurve.IsPullbackVia (f : T →+* T') A' A'' hA)
        (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T') E E''
          (hE ≫ gE))
        (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T') A A''
          (hA ≫ gA))
        (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hψ : ψ ≫ A''.f = E''.f)
        (hq : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' ψ ψ')
        (hm : FakeEllipticCurve.PreservesLevel E'' A'' ψ hψ),
        ψ ≫ hA = hE ≫ φ → ψ' ≫ hE = hA ≫ φ' →
        (pt T' E'' A'' (hE ≫ gE) hgE'' (hA ≫ gA) hgA'' ψ ψ' hψ hq
          hm).left =
          Spec.map (CommRingCat.ofHom (f : T →+* T')) ≫
            (pt T E' A' gE hgE gA hgA φ φ' hφ hp hl).left) ∧
      (∀ (T : Type) [CommRing T] [Algebra S T]
        (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A)
        (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
        (gA : A'.A ⟶ A.A)
        (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
        (z : SchemeHomOver
          (Spec.map (CommRingCat.ofHom (algebraMap S T))) ξ),
        ∃ (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
          (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ')
          (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ),
          pt T E' A' gE hgE gA hgA φ φ' hφ hp hl = z) ∧
      (∀ (T : Type) [CommRing T] [Algebra S T]
        (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A)
        (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
        (gA : A'.A ⟶ A.A)
        (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
        (φ₁ : E'.A ⟶ A'.A) (φ₁' : A'.A ⟶ E'.A) (hφ₁ : φ₁ ≫ A'.f = E'.f)
        (hp₁ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ₁ φ₁')
        (hl₁ : FakeEllipticCurve.PreservesLevel E' A' φ₁ hφ₁)
        (φ₂ : E'.A ⟶ A'.A) (φ₂' : A'.A ⟶ E'.A) (hφ₂ : φ₂ ≫ A'.f = E'.f)
        (hp₂ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ₂ φ₂')
        (hl₂ : FakeEllipticCurve.PreservesLevel E' A' φ₂ hφ₂),
        pt T E' A' gE hgE gA hgA φ₁ φ₁' hφ₁ hp₁ hl₁ =
          pt T E' A' gE hgE gA hgA φ₂ φ₂' hφ₂ hp₂ hl₂ →
          φ₁ = φ₂ ∧ φ₁' = φ₂') :=
  FakeEllipticCurve.IsogenyPair.representsOn_iff r d E A ξ pt

section Representability

variable {S : Type} [CommRing S] {r d : ℕ} {E A : FakeEllipticCurve Λ N S}
  {X : Scheme.{0}} {ξ : X ⟶ Spec (CommRingCat.of S)}
  {pt : FakeEllipticCurve.IsogenyPair.PtFamily r d E A ξ}
  {T : Type} [CommRing T] [Algebra S T]
  {E' A' : FakeEllipticCurve Λ N T} {gE : E'.A ⟶ E.A}
  {hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE}
  {gA : A'.A ⟶ A.A}
  {hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA}

/-- Isomorphism invariance, for isomorphisms of the pullbacks compatible with
their maps to `E` and `A`, takes both commuting squares: the one for the
forward maps and the one for the reverse maps. -/
example (h : FakeEllipticCurve.IsogenyPair.RepresentsOn r d E A ξ pt)
    (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
    (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ')
    (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ)
    (E'' A'' : FakeEllipticCurve Λ N T) (gE'' : E''.A ⟶ E.A)
    (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E'' gE'')
    (gA'' : A''.A ⟶ A.A)
    (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' gA'')
    (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hψ : ψ ≫ A''.f = E''.f)
    (hq : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' ψ ψ')
    (hm : FakeEllipticCurve.PreservesLevel E'' A'' ψ hψ)
    (iE : E'.A ≅ E''.A) (hiE : iE.hom ≫ E''.f = E'.f)
    (iA : A'.A ≅ A''.A) (hiA : iA.hom ≫ A''.f = A'.f)
    (hisoE : FakeEllipticCurve.IsoVia E' E'' iE hiE)
    (hisoA : FakeEllipticCurve.IsoVia A' A'' iA hiA)
    (hgE' : iE.hom ≫ gE'' = gE) (hgA' : iA.hom ≫ gA'' = gA)
    (hfwd : iE.hom ≫ ψ = φ ≫ iA.hom) (hrev : iA.hom ≫ ψ' = φ' ≫ iE.hom) :
    pt T E' A' gE hgE gA hgA φ φ' hφ hp hl =
      pt T E'' A'' gE'' hgE'' gA'' hgA'' ψ ψ' hψ hq hm :=
  h.1 T E' A' gE hgE gA hgA φ φ' hφ hp hl E'' A'' gE'' hgE'' gA'' hgA'' ψ ψ'
    hψ hq hm iE hiE iA hiA hisoE hisoA hgE' hgA' hfwd hrev

/-- The reverse square is a separate condition: it follows from the forward
square, the composites of both pairs and the compatibility of `iE` with the
action of `Λ` when the forward map `φ` is an epimorphism. -/
example (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) [Epi φ]
    (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ')
    {E'' A'' : FakeEllipticCurve Λ N T} (ψ : E''.A ⟶ A''.A)
    (ψ' : A''.A ⟶ E''.A)
    (hq : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' ψ ψ')
    (iE : E'.A ≅ E''.A) (hiE : iE.hom ≫ E''.f = E'.f) (iA : A'.A ≅ A''.A)
    (hisoE : FakeEllipticCurve.IsoVia E' E'' iE hiE)
    (hfwd : iE.hom ≫ ψ = φ ≫ iA.hom) : iA.hom ≫ ψ' = φ' ≫ iE.hom := by
  obtain ⟨_, _, _, _, _, _, _, hφφ', _⟩ := hp
  obtain ⟨_, _, _, _, _, _, _, hψψ', _⟩ := hq
  rw [← cancel_epi φ, ← Category.assoc, ← hfwd, Category.assoc, hψψ',
    ← Category.assoc, hφφ', hisoE.2.1]

/-- Naturality in the base ring compares the points of two pairs related by
commuting squares for both maps. -/
example (h : FakeEllipticCurve.IsogenyPair.RepresentsOn r d E A ξ pt)
    (T' : Type) [CommRing T'] [Algebra S T'] (f : T →ₐ[S] T')
    (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
    (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ')
    (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ)
    (E'' A'' : FakeEllipticCurve Λ N T') (hE : E''.A ⟶ E'.A)
    (hhE : FakeEllipticCurve.IsPullbackVia (f : T →+* T') E' E'' hE)
    (hA : A''.A ⟶ A'.A)
    (hhA : FakeEllipticCurve.IsPullbackVia (f : T →+* T') A' A'' hA)
    (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T') E E''
      (hE ≫ gE))
    (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T') A A''
      (hA ≫ gA))
    (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hψ : ψ ≫ A''.f = E''.f)
    (hq : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' ψ ψ')
    (hm : FakeEllipticCurve.PreservesLevel E'' A'' ψ hψ)
    (hsq : ψ ≫ hA = hE ≫ φ) (hsq' : ψ' ≫ hE = hA ≫ φ') :
    (pt T' E'' A'' (hE ≫ gE) hgE'' (hA ≫ gA) hgA'' ψ ψ' hψ hq hm).left =
      Spec.map (CommRingCat.ofHom (f : T →+* T')) ≫
        (pt T E' A' gE hgE gA hgA φ φ' hφ hp hl).left :=
  h.2.1 T T' f E' A' gE hgE gA hgA φ φ' hφ hp hl E'' A'' hE hhE hA hhA hgE''
    hgA'' ψ ψ' hψ hq hm hsq hsq'

/-- Equal points determine the reverse map of the pair. -/
example (h : FakeEllipticCurve.IsogenyPair.RepresentsOn r d E A ξ pt)
    (φ₁ : E'.A ⟶ A'.A) (φ₁' : A'.A ⟶ E'.A) (hφ₁ : φ₁ ≫ A'.f = E'.f)
    (hp₁ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ₁ φ₁')
    (hl₁ : FakeEllipticCurve.PreservesLevel E' A' φ₁ hφ₁)
    (φ₂ : E'.A ⟶ A'.A) (φ₂' : A'.A ⟶ E'.A) (hφ₂ : φ₂ ≫ A'.f = E'.f)
    (hp₂ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ₂ φ₂')
    (hl₂ : FakeEllipticCurve.PreservesLevel E' A' φ₂ hφ₂)
    (heq : pt T E' A' gE hgE gA hgA φ₁ φ₁' hφ₁ hp₁ hl₁ =
      pt T E' A' gE hgE gA hgA φ₂ φ₂' hφ₂ hp₂ hl₂) :
    φ₁' = φ₂' :=
  (h.2.2.2 T E' A' gE hgE gA hgA φ₁ φ₁' hφ₁ hp₁ hl₁ φ₂ φ₂' hφ₂ hp₂ hl₂
    heq).2

end Representability

end QMIsogenyTest
