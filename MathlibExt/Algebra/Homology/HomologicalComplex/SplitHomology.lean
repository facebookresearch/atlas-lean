/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologicalComplex.Splitting
public import MathlibExt.Algebra.Homology.HomologicalComplex.HomologyProjection

/-!
# Split complexes and their homology

In a preadditive category, a splitting of a complex K gives normalized
cycles retractions and homology inclusions at each degree with homology.
When homology exists in every degree, these maps form a projection onto
and inclusion from the zero-differential complex H(K).

The inclusion followed by projection is the identity of H(K); the reverse
composite is homotopic to the identity of K. The two morphisms are
quasi-isomorphisms and give a homotopy equivalence K ≃ H(K). Conversely,
a homotopy equivalence with a zero-differential complex yields a splitting.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe u v w

variable {C : Type u} [Category.{v} C]
  {ι : Type w} {c : ComplexShape ι}

section Preadditive

variable [Preadditive C] {K L : HomologicalComplex C c}

/--
Let K and L be complexes of the same shape c in a preadditive category C. Assume every
differential of L vanishes and let e be a homotopy equivalence K ≃ L. If H is its homotopy
from e.hom ≫ e.inv to 1_K, the reversed homotopy has components −Hᵢⱼ and gives a
generalized-inverse splitting of K.
-/
def Splitting.ofZeroDifferentialHomotopyEquiv
    (hL : ∀ i j : ι, L.d i j = 0) (e : HomotopyEquiv K L) : Splitting K where
  hom := e.homotopyHomInvId.symm.hom
  zero := e.homotopyHomInvId.symm.zero
  d_h_d i j := by
    let h : Homotopy (𝟙 K) (e.hom ≫ e.inv) := e.homotopyHomInvId.symm
    by_cases hij : c.Rel i j
    · have hId := h.comm j
      simp only [HomologicalComplex.id_f] at hId
      have hq : K.d i j ≫ (e.hom ≫ e.inv).f j = 0 := by
        change K.d i j ≫ (e.hom.f j ≫ e.inv.f j) = 0
        rw [← Category.assoc, ← e.hom.comm i j, hL i j, comp_zero, zero_comp]
      have hd : K.d i j ≫ dNext j h.hom = 0 := by
        change K.d i j ≫ (K.d j (c.next j) ≫ h.hom (c.next j) j) = 0
        rw [← Category.assoc, K.d_comp_d, zero_comp]
      have hp : prevD j h.hom = h.hom j i ≫ K.d i j := prevD_eq h.hom hij
      have he := congrArg (fun a : K.X j ⟶ K.X j => K.d i j ≫ a) hId
      simp only [Category.comp_id, Preadditive.comp_add, hq, hd, zero_add] at he
      rw [hp] at he
      dsimp only [h] at he
      simpa only [Category.assoc, add_zero] using he.symm
    · rw [K.shape i j hij]
      simp only [comp_zero]

/--
Let K and L be complexes of the same shape c in a preadditive category C. Assume L has zero
differentials and e is a homotopy equivalence from K to L. The induced splitting has component
−e.homotopyHomInvId.hom i j : Kᵢ → Kⱼ; the minus sign reverses the homotopy from e.hom ≫ e.inv
to 1_K.
-/
lemma Splitting.ofZeroDifferentialHomotopyEquiv_hom
    (hL : ∀ i j : ι, L.d i j = 0) (e : HomotopyEquiv K L) (i j : ι) :
    (Splitting.ofZeroDifferentialHomotopyEquiv hL e).hom i j =
      -e.homotopyHomInvId.hom i j := rfl

/--
Let K and L be complexes of the same shape c in a preadditive category C. If all differentials
of L vanish and K is homotopy equivalent to L, then K admits a splitting whose reverse-degree
maps satisfy d h d = d.
-/
lemma isSplit_of_homotopyEquiv_zeroDifferential
    (hL : ∀ i j : ι, L.d i j = 0) (e : HomotopyEquiv K L) : IsSplit K :=
  ⟨Splitting.ofZeroDifferentialHomotopyEquiv hL e⟩

end Preadditive

section Pointwise

variable [Preadditive C] {K : HomologicalComplex C c}

noncomputable section

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ for its cycles, Hᵢ for its homology, jᵢ : Zᵢ → Kᵢ
for the cycle inclusion and πᵢ : Zᵢ → Hᵢ for the homology quotient. Let n be the normalized
splitting and Dᵢ = dᵢ,next(i) ≫ n.hom next(i) i. The endomorphism 1_{Kᵢ} − Dᵢ factors through
jᵢ, giving rᵢ : Kᵢ → Zᵢ with rᵢ ≫ jᵢ = 1_{Kᵢ} − Dᵢ.
-/
def Splitting.cyclesRetraction (s : Splitting K) (i : ι) [K.HasHomology i] : K.X i ⟶ K.cycles i :=
  K.liftCycles (𝟙 (K.X i) - dNext i s.normalize.hom) (c.next i) rfl (by
    change (𝟙 (K.X i) - K.d i (c.next i) ≫ s.normalize.hom (c.next i) i) ≫
      K.d i (c.next i) = 0
    rw [Preadditive.sub_comp, Category.id_comp]
    rw [Category.assoc, s.normalize.d_h_d i (c.next i), sub_self])

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ for its cycles, Hᵢ for its homology, jᵢ : Zᵢ → Kᵢ
for the cycle inclusion and πᵢ : Zᵢ → Hᵢ for the homology quotient. For the cycles retraction
rᵢ constructed from s.normalize, rᵢ ≫ jᵢ = 1_{Kᵢ} − dᵢ,next(i) ≫ s.normalize.hom next(i) i.
Thus it selects the complement of the normalized outgoing projector.
-/
@[reassoc]
lemma Splitting.cyclesRetraction_iCycles (s : Splitting K) (i : ι) [K.HasHomology i] :
    s.cyclesRetraction i ≫ K.iCycles i = 𝟙 (K.X i) - dNext i s.normalize.hom :=
  K.liftCycles_i _ _ _ _

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ for its cycles, Hᵢ for its homology, jᵢ : Zᵢ → Kᵢ
for the cycle inclusion and πᵢ : Zᵢ → Hᵢ for the homology quotient. The normalized cycles
retraction rᵢ : Kᵢ → Zᵢ splits the inclusion: jᵢ ≫ rᵢ = 1_{Zᵢ}.
-/
@[reassoc]
lemma Splitting.iCycles_cyclesRetraction (s : Splitting K) (i : ι) [K.HasHomology i] :
    K.iCycles i ≫ s.cyclesRetraction i = 𝟙 (K.cycles i) := by
  have ha : K.iCycles i ≫ dNext i s.normalize.hom = 0 := by
    change K.iCycles i ≫ (K.d i (c.next i) ≫ s.normalize.hom (c.next i) i) = 0
    rw [← Category.assoc, K.iCycles_d, zero_comp]
  apply (cancel_mono (K.iCycles i)).1
  calc
    _ = K.iCycles i ≫ (𝟙 (K.X i) - dNext i s.normalize.hom) := by
      rw [Category.assoc, s.cyclesRetraction_iCycles i]
    _ = K.iCycles i := by rw [Preadditive.comp_sub, Category.comp_id, ha, sub_zero]
    _ = 𝟙 (K.cycles i) ≫ K.iCycles i := (Category.id_comp _).symm

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ for its cycles, Hᵢ for its homology, jᵢ : Zᵢ → Kᵢ
for the cycle inclusion and πᵢ : Zᵢ → Hᵢ for the homology quotient. Let Bᵢ = s.normalize.hom i
prev(i) ≫ d_prev(i),i. The map jᵢ ≫ (1_{Kᵢ} − Bᵢ) descends through πᵢ, defining ℓᵢ : Hᵢ → Kᵢ
with πᵢ ≫ ℓᵢ = jᵢ ≫ (1_{Kᵢ} − Bᵢ).
-/
def Splitting.homologyInclusionComponent (s : Splitting K) (i : ι) [K.HasHomology i] :
    K.homology i ⟶ K.X i :=
  (K.sc i).descHomology (K.iCycles i ≫ (𝟙 (K.X i) - prevD i s.normalize.hom)) (by
    have hFactor : (K.sc i).toCycles ≫ K.iCycles i = K.d (c.prev i) i :=
      (K.sc i).toCycles_i
    have hZero : K.d (c.prev i) i ≫
        (𝟙 (K.X i) - s.normalize.hom i (c.prev i) ≫ K.d (c.prev i) i) = 0 := by
      rw [Preadditive.comp_sub, Category.comp_id,
        s.normalize.d_h_d (c.prev i) i, sub_self]
    have h := congrArg
      (fun f : K.X (c.prev i) ⟶ K.X i => f ≫
        (𝟙 (K.X i) - prevD i s.normalize.hom)) hFactor
    change (K.sc i).toCycles ≫
      (K.iCycles i ≫ (𝟙 (K.X i) - prevD i s.normalize.hom)) = 0
    exact (Category.assoc (K.sc i).toCycles (K.iCycles i)
      (𝟙 (K.X i) - prevD i s.normalize.hom)).symm.trans (h.trans hZero))

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ for its cycles, Hᵢ for its homology, jᵢ : Zᵢ → Kᵢ
for the cycle inclusion and πᵢ : Zᵢ → Hᵢ for the homology quotient. The homology inclusion ℓᵢ
from s satisfies πᵢ ≫ ℓᵢ = jᵢ ≫ (1_{Kᵢ} − Bᵢ), where Bᵢ = s.normalize.hom i prev(i) ≫
d_prev(i),i is the normalized incoming projector.
-/
@[reassoc]
lemma Splitting.homologyπ_homologyInclusionComponent (s : Splitting K) (i : ι) [K.HasHomology i] :
    K.homologyπ i ≫ s.homologyInclusionComponent i =
      K.iCycles i ≫ (𝟙 (K.X i) - prevD i s.normalize.hom) :=
  (K.sc i).π_descHomology _ _

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume homology exists at degree i. Write Zᵢ for its cycles, Hᵢ for its homology, jᵢ : Zᵢ → Kᵢ
for the cycle inclusion and πᵢ : Zᵢ → Hᵢ for the homology quotient. For the homology inclusion
ℓᵢ : Hᵢ → Kᵢ constructed from s.normalize, every outgoing differential vanishes on its image:
ℓᵢ ≫ K.d i j = 0 for all j.
-/
@[reassoc]
lemma Splitting.homologyInclusionComponent_d (s : Splitting K) (i j : ι) [K.HasHomology i] :
    s.homologyInclusionComponent i ≫ K.d i j = 0 := by
  have hb : prevD i s.normalize.hom ≫ K.d i j = 0 := by
    change (s.normalize.hom i (c.prev i) ≫ K.d (c.prev i) i) ≫ K.d i j = 0
    rw [Category.assoc, K.d_comp_d, comp_zero]
  apply (cancel_epi (K.homologyπ i)).1
  calc
    _ = (K.iCycles i ≫ (𝟙 (K.X i) - prevD i s.normalize.hom)) ≫ K.d i j := by
      rw [← Category.assoc, s.homologyπ_homologyInclusionComponent i]
    _ = K.iCycles i ≫ K.d i j := by
      rw [Category.assoc, Preadditive.sub_comp, Category.id_comp, hb, sub_zero]
    _ = 0 := K.iCycles_d i j
    _ = K.homologyπ i ≫ 0 := comp_zero.symm

end

end Pointwise

section NativeHomology

variable [Preadditive C] {K : HomologicalComplex C c} [∀ i, K.HasHomology i]

noncomputable section

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume K has homology at every degree. Let H(K) be the complex of its homology objects with
zero differentials. The normalized cycles retractions rᵢ : Kᵢ → Zᵢ followed by the quotients
πᵢ : Zᵢ → Hᵢ assemble into a complex morphism Π : K → H(K). Its degree-i component is rᵢ ≫ πᵢ.
-/
def Splitting.homologyProjection (s : Splitting K) : K ⟶ homologyZeroComplex K where
  f i := s.cyclesRetraction i ≫ K.homologyπ i
  comm' i j _ := by
    change (s.cyclesRetraction i ≫ K.homologyπ i) ≫
        (0 : K.homology i ⟶ K.homology j) =
      K.d i j ≫ (s.cyclesRetraction j ≫ K.homologyπ j)
    rw [comp_zero]
    symm
    calc
      _ = K.toCycles i j ≫ (K.iCycles j ≫ s.cyclesRetraction j) ≫ K.homologyπ j := by
        rw [← K.toCycles_i i j]
        simp only [Category.assoc]
      _ = K.toCycles i j ≫ K.homologyπ j := by
        rw [s.iCycles_cyclesRetraction j, Category.id_comp]
      _ = 0 := K.toCycles_comp_homologyπ i j

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume K has homology at every degree. Let H(K) be the complex of its homology objects with
zero differentials. The canonical projection Π : K → H(K) has component Π.f i =
s.cyclesRetraction i ≫ K.homologyπ i, from Kᵢ through its cycles to Hᵢ.
-/
lemma Splitting.homologyProjection_f (s : Splitting K) (i : ι) :
    s.homologyProjection.f i = s.cyclesRetraction i ≫ K.homologyπ i := rfl

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume K has homology at every degree. Let H(K) be the complex of its homology objects with
zero differentials. At every degree i, restricting the projection Π : K → H(K) to cycles gives
the original quotient: K.iCycles i ≫ Π.f i = K.homologyπ i.
-/
@[reassoc]
lemma Splitting.iCycles_homologyProjection_f (s : Splitting K) (i : ι) :
    K.iCycles i ≫ s.homologyProjection.f i = K.homologyπ i := by
  change K.iCycles i ≫ (s.cyclesRetraction i ≫ K.homologyπ i) = K.homologyπ i
  rw [← Category.assoc, s.iCycles_cyclesRetraction i, Category.id_comp]

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume K has homology at every degree. Let H(K) be the complex of its homology objects with
zero differentials. The projection Π : K → H(K) kills every incoming differential: K.d i j ≫
Π.f j = 0 for all i,j, because H(K) has zero differential.
-/
@[reassoc]
lemma Splitting.d_homologyProjection_f (s : Splitting K) (i j : ι) :
    K.d i j ≫ s.homologyProjection.f j = 0 := by
  have h : s.homologyProjection.f i ≫ (0 : K.homology i ⟶ K.homology j) =
      K.d i j ≫ s.homologyProjection.f j := s.homologyProjection.comm i j
  exact h.symm.trans comp_zero

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume K has homology at every degree. Let H(K) be the complex of its homology objects with
zero differentials. The maps ℓᵢ : Hᵢ → Kᵢ descending the normalized complements of incoming
boundaries assemble into a complex morphism ℓ : H(K) → K.
-/
def Splitting.homologyInclusion (s : Splitting K) : homologyZeroComplex K ⟶ K where
  f i := s.homologyInclusionComponent i
  comm' i j _ := by
    change s.homologyInclusionComponent i ≫ K.d i j =
      (0 : K.homology i ⟶ K.homology j) ≫ s.homologyInclusionComponent j
    rw [zero_comp]
    exact s.homologyInclusionComponent_d i j

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume K has homology at every degree. Let H(K) be the complex of its homology objects with
zero differentials. The canonical inclusion ℓ : H(K) → K has degree-i component ℓ.f i =
s.homologyInclusionComponent i : Hᵢ → Kᵢ.
-/
lemma Splitting.homologyInclusion_f (s : Splitting K) (i : ι) :
    s.homologyInclusion.f i = s.homologyInclusionComponent i := rfl

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume K has homology at every degree. Let H(K) be the complex of its homology objects with
zero differentials. Write Π : K → H(K) for the projection with components rᵢ ≫ πᵢ, where rᵢ :
Kᵢ → Zᵢ is the normalized cycles retraction, and ℓ : H(K) → K for the normalized homology
inclusion. The composite on the homology complex is the identity: ℓ ≫ Π = 1_{H(K)}.
-/
lemma Splitting.homologyInclusion_homologyProjection (s : Splitting K) :
    s.homologyInclusion ≫ s.homologyProjection = 𝟙 (homologyZeroComplex K) := by
  apply HomologicalComplex.Hom.ext
  funext i
  change s.homologyInclusionComponent i ≫ s.homologyProjection.f i = 𝟙 (K.homology i)
  have hb : prevD i s.normalize.hom ≫ s.homologyProjection.f i = 0 := by
    change (s.normalize.hom i (c.prev i) ≫ K.d (c.prev i) i) ≫
      s.homologyProjection.f i = 0
    rw [Category.assoc, s.d_homologyProjection_f (c.prev i) i, comp_zero]
  have hDescent := s.homologyπ_homologyInclusionComponent i
  have hCycle := s.iCycles_homologyProjection_f i
  have sectionIdentity {Z H X : C} (π : Z ⟶ H) [Epi π]
      (ι : Z ⟶ X) (a : H ⟶ X) (p : X ⟶ H) (b : X ⟶ X)
      (hDescent : π ≫ a = ι ≫ (𝟙 X - b)) (hCycle : ι ≫ p = π)
      (hb : b ≫ p = 0) : a ≫ p = 𝟙 H := by
    apply (cancel_epi π).1
    rw [← Category.assoc, hDescent, Category.assoc,
      Preadditive.sub_comp, Category.id_comp, hb, sub_zero, hCycle, Category.comp_id]
  exact sectionIdentity (K.homologyπ i) (K.iCycles i)
    (s.homologyInclusionComponent i) (s.homologyProjection.f i)
    (prevD i s.normalize.hom) hDescent hCycle hb

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume K has homology at every degree. Let H(K) be the complex of its homology objects with
zero differentials. Write Π : K → H(K) for the projection with components rᵢ ≫ πᵢ, where rᵢ :
Kᵢ → Zᵢ is the normalized cycles retraction, and ℓ : H(K) → K for the normalized homology
inclusion. The endomorphism Π ≫ ℓ of K is idempotent: (Π ≫ ℓ) ≫ (Π ≫ ℓ) = Π ≫ ℓ.
-/
lemma Splitting.homologyProjectionInclusion_idempotent (s : Splitting K) :
    (s.homologyProjection ≫ s.homologyInclusion) ≫
        (s.homologyProjection ≫ s.homologyInclusion) =
      s.homologyProjection ≫ s.homologyInclusion := by
  calc
    _ = s.homologyProjection ≫
        (s.homologyInclusion ≫ s.homologyProjection) ≫ s.homologyInclusion := by
      simp only [Category.assoc]
    _ = s.homologyProjection ≫ s.homologyInclusion := by
      rw [s.homologyInclusion_homologyProjection, Category.id_comp]

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume K has homology at every degree. Let H(K) be the complex of its homology objects with
zero differentials. Write Π : K → H(K) for the projection with components rᵢ ≫ πᵢ, where rᵢ :
Kᵢ → Zᵢ is the normalized cycles retraction, and ℓ : H(K) → K for the normalized homology
inclusion. At degree i, Π.f i ≫ ℓ.f i = 1_{Kᵢ} − (Dᵢ + Bᵢ), where Dᵢ = dᵢ,next(i) ≫
s.normalize.hom next(i) i and Bᵢ = s.normalize.hom i prev(i) ≫ d_prev(i),i.
-/
lemma Splitting.homologyProjection_comp_homologyInclusion_f (s : Splitting K) (i : ι) :
    s.homologyProjection.f i ≫ s.homologyInclusion.f i =
      𝟙 (K.X i) - (dNext i s.normalize.hom + prevD i s.normalize.hom) := by
  let a : K.X i ⟶ K.X i := dNext i s.normalize.hom
  let b : K.X i ⟶ K.X i := prevD i s.normalize.hom
  have hab : a ≫ b = 0 := by
    change (K.d i (c.next i) ≫ s.normalize.hom (c.next i) i) ≫
      (s.normalize.hom i (c.prev i) ≫ K.d (c.prev i) i) = 0
    calc
      _ = K.d i (c.next i) ≫
          (s.normalize.hom (c.next i) i ≫ s.normalize.hom i (c.prev i)) ≫
            K.d (c.prev i) i := by simp only [Category.assoc]
      _ = 0 := by
        rw [s.normalize_hom_comp_hom (c.next i) i (c.prev i)]
        simp only [zero_comp, comp_zero]
  change (s.cyclesRetraction i ≫ K.homologyπ i) ≫
    s.homologyInclusionComponent i = 𝟙 (K.X i) - (a + b)
  calc
    _ = s.cyclesRetraction i ≫ (K.iCycles i ≫ (𝟙 (K.X i) - b)) := by
      rw [Category.assoc, s.homologyπ_homologyInclusionComponent i]
    _ = (𝟙 (K.X i) - a) ≫ (𝟙 (K.X i) - b) := by
      rw [← Category.assoc, s.cyclesRetraction_iCycles i]
    _ = 𝟙 (K.X i) - (a + b) := by
      simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp,
        Category.comp_id, hab]
      abel

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume K has homology at every degree. Let H(K) be the complex of its homology objects with
zero differentials. Write Π : K → H(K) for the projection with components rᵢ ≫ πᵢ, where rᵢ :
Kᵢ → Zᵢ is the normalized cycles retraction, and ℓ : H(K) → K for the normalized homology
inclusion. The normalized inverse family n = s.normalize.hom is a homotopy from 1_K to Π ≫ ℓ:
at degree i, 1_{Kᵢ} = (Π ≫ ℓ).f i + dNext i n + prevD i n.
-/
def Splitting.homotopyIdHomologyProjectionInclusion (s : Splitting K) :
    Homotopy (𝟙 K) (s.homologyProjection ≫ s.homologyInclusion) where
  hom := s.normalize.hom
  zero := s.normalize.zero
  comm i := by
    rw [HomologicalComplex.id_f, HomologicalComplex.comp_f,
      s.homologyProjection_comp_homologyInclusion_f i]
    abel

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume K has homology at every degree. Let H(K) be the complex of its homology objects with
zero differentials. Write Π : K → H(K) for the projection with components rᵢ ≫ πᵢ, where rᵢ :
Kᵢ → Zᵢ is the normalized cycles retraction, and ℓ : H(K) → K for the normalized homology
inclusion. These morphisms give a homotopy equivalence K ≃ H(K). The composite ℓ ≫ Π is
exactly the identity of H(K), and Π ≫ ℓ is homotopic to 1_K through the normalized splitting.
-/
def Splitting.homotopyEquivHomology (s : Splitting K) :
    HomotopyEquiv K (homologyZeroComplex K) where
  hom := s.homologyProjection
  inv := s.homologyInclusion
  homotopyHomInvId := s.homotopyIdHomologyProjectionInclusion.symm
  homotopyInvHomId := Homotopy.ofEq (s.homologyInclusion_homologyProjection)

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume K has homology at every degree. Let H(K) be the complex of its homology objects with
zero differentials. Write Π : K → H(K) for the projection with components rᵢ ≫ πᵢ, where rᵢ :
Kᵢ → Zᵢ is the normalized cycles retraction, and ℓ : H(K) → K for the normalized homology
inclusion. The forward morphism of the constructed homotopy equivalence K ≃ H(K) is precisely
Π = s.homologyProjection.
-/
lemma Splitting.homotopyEquivHomology_hom (s : Splitting K) :
    s.homotopyEquivHomology.hom = s.homologyProjection := rfl

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume K has homology at every degree. Let H(K) be the complex of its homology objects with
zero differentials. Write Π : K → H(K) for the projection with components rᵢ ≫ πᵢ, where rᵢ :
Kᵢ → Zᵢ is the normalized cycles retraction, and ℓ : H(K) → K for the normalized homology
inclusion. The reverse morphism of the constructed homotopy equivalence K ≃ H(K) is precisely
ℓ = s.homologyInclusion.
-/
lemma Splitting.homotopyEquivHomology_inv (s : Splitting K) :
    s.homotopyEquivHomology.inv = s.homologyInclusion := rfl

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume K has homology at every degree. Let H(K) be the complex of its homology objects with
zero differentials. Write Π : K → H(K) for the projection with components rᵢ ≫ πᵢ, where rᵢ :
Kᵢ → Zᵢ is the normalized cycles retraction, and ℓ : H(K) → K for the normalized homology
inclusion. The homotopy from Π ≫ ℓ to 1_K in this equivalence has component −s.normalize.hom i
j at every pair i,j. It is the negative of the homotopy from 1_K to Π ≫ ℓ.
-/
lemma Splitting.homotopyEquivHomology_homotopyHomInvId_hom
    (s : Splitting K) (i j : ι) :
    s.homotopyEquivHomology.homotopyHomInvId.hom i j = -s.normalize.hom i j := rfl

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume K has homology at every degree. Let H(K) be the complex of its homology objects with
zero differentials. Write Π : K → H(K) for the projection with components rᵢ ≫ πᵢ, where rᵢ :
Kᵢ → Zᵢ is the normalized cycles retraction, and ℓ : H(K) → K for the normalized homology
inclusion. Let ηᵢ : Hᵢ(H(K)) ≅ Hᵢ(K) be the canonical identification for a zero-differential
complex. The induced projection map satisfies Hᵢ(Π) ≫ ηᵢ.hom = 1_{Hᵢ(K)}.
-/
@[reassoc]
lemma Splitting.homologyProjection_homologyMap_hom (s : Splitting K) (i : ι) :
    homologyMap s.homologyProjection i ≫
        (homologyZeroComplexHomologyIso K i).hom = 𝟙 (K.homology i) := by
  let L : HomologicalComplex C c := homologyZeroComplex K
  let q : K ⟶ L := s.homologyProjection
  let e : L.homology i ≅ K.homology i := homologyZeroComplexHomologyIso K i
  let π : K.cycles i ⟶ K.homology i := K.homologyπ i
  let π' : L.cycles i ⟶ L.homology i := L.homologyπ i
  let z : K.cycles i ⟶ L.cycles i := cyclesMap q i
  let m : K.homology i ⟶ L.homology i := homologyMap q i
  have hm : π ≫ m = z ≫ π' := homologyπ_naturality q i
  have he : π' ≫ e.hom = L.iCycles i := homologyZeroComplexHomologyIso_π K i
  have hz : z ≫ L.iCycles i = K.iCycles i ≫ q.f i := cyclesMap_i q i
  have hq : K.iCycles i ≫ q.f i = π := s.iCycles_homologyProjection_f i
  apply (cancel_epi π).1
  change π ≫ (m ≫ e.hom) = π ≫ 𝟙 (K.homology i)
  have hFirst : π ≫ (m ≫ e.hom) = (π ≫ m) ≫ e.hom :=
    (Category.assoc π m e.hom).symm
  have hMap : (π ≫ m) ≫ e.hom = (z ≫ π') ≫ e.hom :=
    congrArg (fun t : K.cycles i ⟶ L.homology i => t ≫ e.hom) hm
  have hAssoc : (z ≫ π') ≫ e.hom = z ≫ (π' ≫ e.hom) :=
    Category.assoc z π' e.hom
  let ιL : L.cycles i ⟶ K.homology i := L.iCycles i
  have hCycle : z ≫ (π' ≫ e.hom) = z ≫ ιL :=
    congrArg (fun t : L.cycles i ⟶ K.homology i => z ≫ t) he
  have hNative : z ≫ ιL = K.iCycles i ≫ q.f i := hz
  have hLast : π = π ≫ 𝟙 (K.homology i) := (Category.comp_id π).symm
  exact hFirst.trans (hMap.trans (hAssoc.trans
    (hCycle.trans (hNative.trans (hq.trans hLast)))))

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume K has homology at every degree. Let H(K) be the complex of its homology objects with
zero differentials. Write Π : K → H(K) for the projection with components rᵢ ≫ πᵢ, where rᵢ :
Kᵢ → Zᵢ is the normalized cycles retraction, and ℓ : H(K) → K for the normalized homology
inclusion. For the canonical identification ηᵢ : Hᵢ(H(K)) ≅ Hᵢ(K), the induced map on homology
is Hᵢ(Π) = ηᵢ.inv.
-/
lemma Splitting.homologyProjection_homologyMap (s : Splitting K) (i : ι) :
    homologyMap s.homologyProjection i = (homologyZeroComplexHomologyIso K i).inv := by
  apply (cancel_mono (homologyZeroComplexHomologyIso K i).hom).1
  exact (s.homologyProjection_homologyMap_hom i).trans
    (homologyZeroComplexHomologyIso K i).inv_hom_id.symm

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume K has homology at every degree. Let H(K) be the complex of its homology objects with
zero differentials. Write Π : K → H(K) for the projection with components rᵢ ≫ πᵢ, where rᵢ :
Kᵢ → Zᵢ is the normalized cycles retraction, and ℓ : H(K) → K for the normalized homology
inclusion. For ηᵢ : Hᵢ(H(K)) ≅ Hᵢ(K), the induced map of the inclusion is Hᵢ(ℓ) = ηᵢ.hom.
-/
lemma Splitting.homologyInclusion_homologyMap (s : Splitting K) (i : ι) :
    homologyMap s.homologyInclusion i = (homologyZeroComplexHomologyIso K i).hom := by
  let e := homologyZeroComplexHomologyIso K i
  have h : homologyMap s.homologyInclusion i ≫ homologyMap s.homologyProjection i =
      𝟙 ((homologyZeroComplex K).homology i) := by
    rw [← homologyMap_comp, s.homologyInclusion_homologyProjection, homologyMap_id]
  apply (cancel_mono e.inv).1
  exact (show homologyMap s.homologyInclusion i ≫ e.inv = 𝟙 _ from by
    simpa only [s.homologyProjection_homologyMap i] using h).trans e.hom_inv_id.symm

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume K has homology at every degree. Let H(K) be the complex of its homology objects with
zero differentials. Write Π : K → H(K) for the projection with components rᵢ ≫ πᵢ, where rᵢ :
Kᵢ → Zᵢ is the normalized cycles retraction, and ℓ : H(K) → K for the normalized homology
inclusion. The projection Π : K → H(K) is a quasi-isomorphism: its induced map on homology is
an isomorphism at every degree.
-/
lemma Splitting.quasiIso_homologyProjection (s : Splitting K) :
    _root_.QuasiIso s.homologyProjection := by
  apply (quasiIso_iff s.homologyProjection).2
  intro i
  apply (quasiIsoAt_iff_isIso_homologyMap s.homologyProjection i).2
  rw [s.homologyProjection_homologyMap i]
  infer_instance

/--
Let K be a complex of shape c in a preadditive category C, let s be a splitting of K, and
assume K has homology at every degree. Let H(K) be the complex of its homology objects with
zero differentials. Write Π : K → H(K) for the projection with components rᵢ ≫ πᵢ, where rᵢ :
Kᵢ → Zᵢ is the normalized cycles retraction, and ℓ : H(K) → K for the normalized homology
inclusion. The inclusion ℓ : H(K) → K is a quasi-isomorphism: its induced map on homology is
an isomorphism at every degree.
-/
lemma Splitting.quasiIso_homologyInclusion (s : Splitting K) :
    _root_.QuasiIso s.homologyInclusion := by
  apply (quasiIso_iff s.homologyInclusion).2
  intro i
  apply (quasiIsoAt_iff_isIso_homologyMap s.homologyInclusion i).2
  rw [s.homologyInclusion_homologyMap i]
  infer_instance

/--
Let K be a complex of arbitrary shape c in a preadditive category C, with homology at every
degree. Then K admits a generalized-inverse splitting if and only if it is homotopy equivalent
to the complex H(K) whose terms are Hᵢ(K) and whose differentials vanish.
-/
lemma isSplit_iff_homotopyEquiv_homologyZeroComplex (K : HomologicalComplex C c)
    [∀ i, K.HasHomology i] :
    IsSplit K ↔ Nonempty (HomotopyEquiv K (homologyZeroComplex K)) := by
  constructor
  · rintro ⟨s⟩
    exact ⟨s.homotopyEquivHomology⟩
  · rintro ⟨e⟩
    exact isSplit_of_homotopyEquiv_zeroDifferential (homologyZeroComplex_d K) e

end

end NativeHomology

end HomologicalComplex
