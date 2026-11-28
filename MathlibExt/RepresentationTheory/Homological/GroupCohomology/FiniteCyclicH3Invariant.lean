/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import
  MathlibExt.RepresentationTheory.Homological.GroupCohomology.CyclicEvenResolutionComparison
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupOneTwo
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.LowDegreeThreeHomologyIso

/-!
# The explicit odd cyclic invariant in degree three

Let k be a commutative ring, G a finite abelian group, A a k-linear representation in universe
u, and g∈G. Put N_G=Σ_hρ(h) and D_g=ρ(g)-id. The three-cocycle invariant ν_g(z)=Σ_hz(g,h,g) lies
in ker(N_G). For a three-coboundary δ₂t, it equals D_g(Σ_ht(h,g)). Thus it induces a k-linear
map H³(G,A)→Q_g(A)=ker(N_G)/im(D_g).

The cochain maps Σ_ht(h,g), Σ_hz(g,h,g), and Σ_aΣ_hw(a,g,h,g) form a morphism from the
degree-three inhomogeneous short complex to A --D_g→ A --N_G→ A. Its concrete homology map is
the invariant descent.

For a cyclic generator g, the periodic-resolution computation also gives a linear equivalence
H³(G,A)≃Q_g(A). The comparison property is equality of this equivalence's linear map with the
explicit invariant descent, and is equivalent to its cyclic-sum formula on every cocycle
representative. Cup representatives of degrees (1,2) and (1,1,1) have explicit norm-kernel and
quotient formulas; the formula for that periodic-resolution equivalence includes the
comparison-property hypothesis.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory MonoidalCategory ShortComplex Limits
open scoped BigOperators

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G]

@[simp]
theorem cyclicSumThree_apply (A : Rep k G) (g : G)
    (z : G × G × G → A) :
    cyclicSumThree A g z = ∑ h : G, z (g, h, g) :=
  rfl

private theorem sum_mulLeft {M : Type*} [AddCommMonoid M]
    (g : G) (f : G → M) :
    (∑ h : G, f (g * h)) = ∑ h : G, f h := by
  simpa using (Equiv.mulLeft g).sum_comp Finset.univ f

private theorem sum_mulRight {M : Type*} [AddCommMonoid M]
    (g : G) (f : G → M) :
    (∑ h : G, f (h * g)) = ∑ h : G, f h := by
  simpa using (Equiv.mulRight g).sum_comp Finset.univ f

/-- Let k be a commutative ring, G a finite abelian group, and A a k-linear G-representation, in
universe u. For g∈G put D_g=ρ(g)-id, N_G=Σ_{h∈G}ρ(h), and Q_g(A)=ker(N_G)/im(D_g). For a
two-cochain t:G²→A, Σ_h(δ₂t)(g,h,g)=ρ(g)(Σ_ht(h,g))-Σ_ht(h,g)=D_g(Σ_ht(h,g)). Hence this cyclic
sum belongs to im(D_g). -/
theorem cyclicSumThree_d₂₃ (A : Rep k G) (g : G)
    (t : G × G → A) :
    cyclicSumThree A g ((d₂₃ A).hom t) =
      A.ρ g (∑ h : G, t (h, g)) - ∑ h : G, t (h, g) := by
  rw [cyclicSumThree_apply]
  simp only [d₂₃_hom_apply, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, map_sum]
  rw [sum_mulLeft g (fun h => t (h, g))]
  rw [sum_mulRight g (fun h => t (g, h))]
  abel

/-- Let k be a commutative ring, G a finite abelian group, and A a k-linear G-representation, in
universe u. For g∈G, the k-linear map σ₄^g:C⁴(G,A)→A sends w to Σ_{a∈G}Σ_{h∈G}w(a,g,h,g). Its
second and fourth arguments are fixed at g while the first and third range over the entire
group. -/
noncomputable def cyclicSumFour (A : Rep k G) (g : G) :
    ModuleCat.of k (G × G × G × G → A) ⟶ ModuleCat.of k A :=
  ModuleCat.ofHom
    { toFun := fun w => ∑ a : G, ∑ h : G, w (a, g, h, g)
      map_add' := fun x y => by
        simp only [Pi.add_apply, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        simp only [Pi.smul_apply, RingHom.id_apply,
          Finset.smul_sum] }

@[simp]
theorem cyclicSumFour_apply (A : Rep k G) (g : G)
    (w : G × G × G × G → A) :
    cyclicSumFour A g w = ∑ a : G, ∑ h : G, w (a, g, h, g) :=
  rfl

/-- Let k be a commutative ring, G a finite abelian group, and A a k-linear G-representation, in
universe u. For g∈G put D_g=ρ(g)-id, N_G=Σ_{h∈G}ρ(h), and Q_g(A)=ker(N_G)/im(D_g). Let
σ₃^g(z)=Σ_hz(g,h,g) and σ₄^g(w)=Σ_aΣ_hw(a,g,h,g). As maps C³(G,A)→A, σ₃^g≫N_G=δ₃≫σ₄^g.
Equivalently N_G(Σ_hz(g,h,g))=Σ_aΣ_h(δ₃z)(a,g,h,g). -/
theorem cyclicSumThree_comp_norm (A : Rep k G) (g : G) :
    cyclicSumThree A g ≫ A.norm.asHom.toModuleCatHom =
      d₃₄ A ≫ cyclicSumFour A g := by
  ext z
  change A.ρ.norm (∑ h : G, z (g, h, g)) =
    ∑ a : G, ∑ h : G,
      (A.ρ a (z (g, h, g)) - z (a * g, h, g) +
        z (a, g * h, g) - z (a, g, h * g) + z (a, g, h))
  unfold Representation.norm
  simp only [LinearMap.sum_apply]
  have h₁ : (∑ a : G, ∑ h : G, z (a * g, h, g)) =
      ∑ a : G, ∑ h : G, z (a, h, g) := by
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro h _
    exact sum_mulRight g (fun a => z (a, h, g))
  have h₂ : (∑ a : G, ∑ h : G, z (a, g * h, g)) =
      ∑ a : G, ∑ h : G, z (a, h, g) := by
    apply Finset.sum_congr rfl
    intro a _
    exact sum_mulLeft g (fun h => z (a, h, g))
  have h₃ : (∑ a : G, ∑ h : G, z (a, g, h * g)) =
      ∑ a : G, ∑ h : G, z (a, g, h) := by
    apply Finset.sum_congr rfl
    intro a _
    exact sum_mulRight g (fun h => z (a, g, h))
  simp_rw [map_sum]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [h₁, h₂, h₃]
  abel

/-- Let k be a commutative ring, G a finite abelian group, and A a k-linear G-representation, in
universe u. For g∈G put D_g=ρ(g)-id, N_G=Σ_{h∈G}ρ(h), and Q_g(A)=ker(N_G)/im(D_g). The
short-complex morphism (C²(G,A) --δ₂→ C³(G,A) --δ₃→ C⁴(G,A))→(A --D_g→ A --N_G→ A) has
components t↦Σ_ht(h,g), z↦Σ_hz(g,h,g), and w↦Σ_aΣ_hw(a,g,h,g). These components commute with
both differentials. -/
noncomputable def cyclicOddComparisonHom (A : Rep k G) (g : G) :
    shortComplexH3 A ⟶ Rep.FiniteCyclicGroup.subCompNormHom A g where
  τ₁ := cyclicSumTwo A g
  τ₂ := cyclicSumThree A g
  τ₃ := cyclicSumFour A g
  comm₁₂ := cyclicSumTwo_comp_sub A g
  comm₂₃ := cyclicSumThree_comp_norm A g

/-- Let k be a commutative ring, G a finite abelian group, and A a k-linear G-representation, in
universe u. For g∈G and z∈Z³(G,A), Σ_{a∈G}ρ(a)(Σ_{h∈G}z(g,h,g))=0. This is N_G(ν_g(z))=0,
obtained from the identity between the cyclic sum and δ₃ and the cocycle equation δ₃z=0. -/
theorem cyclicSumThree_norm_eq_zero (A : Rep k G) (g : G)
    (z : cocycles₃ A) :
    ∑ a : G, A.ρ a (cyclicSumThree A g z) = 0 := by
  have hcomm := ConcreteCategory.congr_hom
    (cyclicSumThree_comp_norm A g) z
  change A.norm.asHom.hom (cyclicSumThree A g z) =
    cyclicSumFour A g (d₃₄ A z) at hcomm
  rw [Rep.norm_apply, Representation.norm, LinearMap.sum_apply] at hcomm
  calc
    (∑ a : G, A.ρ a (cyclicSumThree A g z)) =
        cyclicSumFour A g (d₃₄ A z) := hcomm
    _ = cyclicSumFour A g 0 := congrArg _ z.property
    _ = 0 := map_zero _

/-- Let k be a commutative ring, G a finite abelian group, and A a k-linear G-representation, in
universe u. For g∈G put D_g=ρ(g)-id, N_G=Σ_{h∈G}ρ(h), and Q_g(A)=ker(N_G)/im(D_g). The k-linear
invariant ν_g:Z³(G,A)→ker(N_G) sends z to Σ_hz(g,h,g), with its norm-kernel property. Its
underlying coefficient value is this cyclic sum. -/
noncomputable def cyclicThreeCocycleInvariant (A : Rep k G) (g : G) :
    cocycles₃ A →ₗ[k] LinearMap.ker A.norm.asHom.hom.toLinearMap :=
  LinearMap.codRestrict (LinearMap.ker A.norm.asHom.hom.toLinearMap)
    ((cyclicSumThree A g).hom.comp (cocycles₃ A).subtype) (fun z => by
    rw [LinearMap.mem_ker]
    change A.norm.asHom.hom (cyclicSumThree A g z) = 0
    rw [Rep.norm_apply]
    rw [Representation.norm]
    rw [LinearMap.sum_apply]
    exact cyclicSumThree_norm_eq_zero A g z)

@[simp]
theorem cyclicThreeCocycleInvariant_coe
    (A : Rep k G) (g : G) (z : cocycles₃ A) :
    (cyclicThreeCocycleInvariant A g z : A) = cyclicSumThree A g z :=
  rfl

/-- Let k be a commutative ring, G a finite abelian group, and A a k-linear G-representation, in
universe u. For g∈G put D_g=ρ(g)-id, N_G=Σ_{h∈G}ρ(h), and Q_g(A)=ker(N_G)/im(D_g). The k-module
Q_g(A) is the concrete homology of A --D_g→ A --N_G→ A. Its representatives are vectors killed
by N_G, and its relations are the image of D_g inside that kernel. -/
noncomputable abbrev cyclicOddQuotient (A : Rep k G) (g : G) : ModuleCat k :=
  (Rep.FiniteCyclicGroup.subCompNormHom A g).moduleCatLeftHomologyData.H

/-- Let k be a commutative ring, G a finite abelian group, and A a k-linear G-representation, in
universe u. For g∈G put D_g=ρ(g)-id, N_G=Σ_{h∈G}ρ(h), and Q_g(A)=ker(N_G)/im(D_g). The k-linear
quotient map q_g:ker(N_G)→Q_g(A) takes a norm-zero representative to its class modulo im(D_g).
It is the concrete homology projection of A --D_g→ A --N_G→ A. -/
noncomputable abbrev cyclicOddHomologyπ (A : Rep k G) (g : G) :
    ↧(LinearMap.ker A.norm.asHom.hom.toLinearMap) ⟶
      cyclicOddQuotient A g :=
  (Rep.FiniteCyclicGroup.subCompNormHom A g).moduleCatLeftHomologyData.π

/-- Let k be a commutative ring, G a finite abelian group, and A a k-linear G-representation, in
universe u. For g∈G put D_g=ρ(g)-id, N_G=Σ_{h∈G}ρ(h), and Q_g(A)=ker(N_G)/im(D_g). For
x∈ker(N_G), q_g(x)=0 if and only if x∈im(D_g), with membership measured in the coefficient
module A. Thus x represents zero exactly when x=ρ(g)a-a for some a∈A. -/
theorem cyclicOddHomologyπ_eq_zero_iff
    (A : Rep k G) (g : G)
    (x : LinearMap.ker A.norm.asHom.hom.toLinearMap) :
    cyclicOddHomologyπ A g x = 0 ↔
      x.1 ∈ LinearMap.range
        (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap := by
  change Submodule.Quotient.mk x = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  change x ∈ LinearMap.range
      (Rep.FiniteCyclicGroup.subCompNormHom A g).moduleCatToCycles ↔ _
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    exact congrArg Subtype.val hy
  · rintro ⟨y, hy⟩
    refine ⟨y, Subtype.ext ?_⟩
    exact hy

/-- Let k be a commutative ring, G a finite abelian group, and A a k-linear G-representation, in
universe u. For g∈G put D_g=ρ(g)-id, N_G=Σ_{h∈G}ρ(h), and Q_g(A)=ker(N_G)/im(D_g). For
z∈Z³(G,A), write ν_g(z)=Σ_{h∈G}z(g,h,g)∈ker(N_G), and q_g:ker(N_G)→Q_g(A) for quotient
projection. For z∈Z³(G,A), if its class π₃(z) in H³(G,A) is zero, then q_g(ν_g(z))=0. A
coboundary cyclic sum is a vector in im(D_g). -/
theorem cyclicOddHomologyπ_cyclicThreeCocycleInvariant_eq_zero
    (A : Rep k G) (g : G)
    (z : cocycles₃ A) (hz : H3π A z = 0) :
    cyclicOddHomologyπ A g (cyclicThreeCocycleInvariant A g z) = 0 := by
  rw [cyclicOddHomologyπ_eq_zero_iff A g]
  obtain ⟨t, ht⟩ := (H3π_eq_zero_iff z).mp hz
  refine ⟨∑ h : G, t (h, g), ?_⟩
  change A.ρ g (∑ h : G, t (h, g)) - ∑ h : G, t (h, g) =
    cyclicSumThree A g z
  rw [← cyclicSumThree_d₂₃ A g t, ht]

/-- Let k be a commutative ring, G a finite abelian group, and A a k-linear G-representation, in
universe u. For g∈G put D_g=ρ(g)-id, N_G=Σ_{h∈G}ρ(h), and Q_g(A)=ker(N_G)/im(D_g). For
z∈Z³(G,A), write ν_g(z)=Σ_{h∈G}z(g,h,g)∈ker(N_G), and q_g:ker(N_G)→Q_g(A) for quotient
projection. For π₃:Z³(G,A)→H³(G,A), ker(π₃)⊆ker(q_g∘ν_g) as k-submodules of Z³(G,A). Every third
coboundary therefore descends to zero in Q_g(A). -/
theorem cyclicThreeCocycleInvariant_ker_le
    (A : Rep k G) (g : G) :
    LinearMap.ker (H3π A).hom ≤
      LinearMap.ker ((cyclicOddHomologyπ A g).hom.comp
        (cyclicThreeCocycleInvariant A g)) := by
  intro z hz
  rw [LinearMap.mem_ker]
  exact cyclicOddHomologyπ_cyclicThreeCocycleInvariant_eq_zero
    A g z hz

/-- Let k be a commutative ring, G a finite abelian group, and A a k-linear G-representation, in
universe u. For g∈G put D_g=ρ(g)-id, N_G=Σ_{h∈G}ρ(h), and Q_g(A)=ker(N_G)/im(D_g). For
z∈Z³(G,A), write ν_g(z)=Σ_{h∈G}z(g,h,g)∈ker(N_G), and q_g:ker(N_G)→Q_g(A) for quotient
projection. The map H³(G,A)→Q_g(A) is induced by the cyclic-sum morphism of short complexes
C²→C³→C⁴ and A --D_g→ A --N_G→ A, using their concrete homology descriptions. It sends π₃(z) to
q_g(ν_g(z)). -/
noncomputable def cyclicOddComparisonQuotientMap
    (A : Rep k G) (g : G) :
    H3 A ⟶ cyclicOddQuotient A g :=
  (H3Iso A).hom ≫
    ShortComplex.leftHomologyMap'
      (cyclicOddComparisonHom A g)
      (shortComplexH3 A).moduleCatLeftHomologyData
      (Rep.FiniteCyclicGroup.subCompNormHom A g).moduleCatLeftHomologyData

/-- Let k be a commutative ring, G a finite abelian group, and A a k-linear G-representation, in
universe u. For g∈G put D_g=ρ(g)-id, N_G=Σ_{h∈G}ρ(h), and Q_g(A)=ker(N_G)/im(D_g). For
z∈Z³(G,A), write ν_g(z)=Σ_{h∈G}z(g,h,g)∈ker(N_G), and q_g:ker(N_G)→Q_g(A) for quotient
projection. On z∈Z³(G,A), the cycle map of the odd cyclic short-complex comparison equals ν_g(z)
in ker(N_G). The comparison therefore preserves the explicit cyclic-sum representative before
quotienting. -/
theorem cyclesMap_cyclicOddComparisonHom_apply
    (A : Rep k G) (g : G) (z : cocycles₃ A) :
    ShortComplex.cyclesMap'
        (cyclicOddComparisonHom A g)
        (shortComplexH3 A).moduleCatLeftHomologyData
        (Rep.FiniteCyclicGroup.subCompNormHom A g).moduleCatLeftHomologyData z =
      cyclicThreeCocycleInvariant A g z := by
  apply Subtype.ext
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Let k be a commutative ring, G a finite abelian group, and A a k-linear G-representation, in
universe u. For g∈G put D_g=ρ(g)-id, N_G=Σ_{h∈G}ρ(h), and Q_g(A)=ker(N_G)/im(D_g). For
z∈Z³(G,A), write ν_g(z)=Σ_{h∈G}z(g,h,g)∈ker(N_G), and q_g:ker(N_G)→Q_g(A) for quotient
projection. For every z∈Z³(G,A), the quotient-valued comparison satisfies
comparison(π₃(z))=q_g(ν_g(z)) in Q_g(A). The left class is inhomogeneous third cohomology and
the right class is the odd periodic coefficient quotient. -/
theorem cyclicOddComparisonQuotientMap_H3π
    (A : Rep k G) (g : G) (z : cocycles₃ A) :
    cyclicOddComparisonQuotientMap A g (H3π A z) =
      cyclicOddHomologyπ A g (cyclicThreeCocycleInvariant A g z) := by
  have hH3m : H3π A ≫ (H3Iso A).hom =
      (shortComplexH3 A).moduleCatLeftHomologyData.π := by
    simp only [H3π, Category.assoc, π_comp_H3Iso_hom,
      Iso.inv_hom_id_assoc]
  have hm : H3π A ≫ cyclicOddComparisonQuotientMap A g =
      ShortComplex.cyclesMap'
          (cyclicOddComparisonHom A g)
          (shortComplexH3 A).moduleCatLeftHomologyData
          (Rep.FiniteCyclicGroup.subCompNormHom A g).moduleCatLeftHomologyData ≫
        (Rep.FiniteCyclicGroup.subCompNormHom A g).moduleCatLeftHomologyData.π := by
    unfold cyclicOddComparisonQuotientMap
    rw [← Category.assoc, hH3m]
    exact ShortComplex.leftHomologyπ_naturality'
      (cyclicOddComparisonHom A g)
      (shortComplexH3 A).moduleCatLeftHomologyData
      (Rep.FiniteCyclicGroup.subCompNormHom A g).moduleCatLeftHomologyData
  have hz := ConcreteCategory.congr_hom hm z
  change cyclicOddComparisonQuotientMap A g (H3π A z) = _
  rw [← cyclesMap_cyclicOddComparisonHom_apply A g z]
  exact hz

/-- Let k be a commutative ring, G a finite abelian group, and A a k-linear G-representation, in
universe u. For g∈G put D_g=ρ(g)-id, N_G=Σ_{h∈G}ρ(h), and Q_g(A)=ker(N_G)/im(D_g). For
z∈Z³(G,A), write ν_g(z)=Σ_{h∈G}z(g,h,g)∈ker(N_G), and q_g:ker(N_G)→Q_g(A) for quotient
projection. The k-linear map F_g:H³(G,A)→Q_g(A) is the descent of q_g∘ν_g through π₃. It is the
underlying linear map of the odd cyclic short-complex quotient comparison. -/
noncomputable def cyclicH3ToOddHomology
    (A : Rep k G) (g : G) :
    H3 A →ₗ[k] cyclicOddQuotient A g :=
  (cyclicOddComparisonQuotientMap A g).hom

/-- Let k be a commutative ring, G a finite abelian group, and A a k-linear G-representation, in
universe u. For g∈G put D_g=ρ(g)-id, N_G=Σ_{h∈G}ρ(h), and Q_g(A)=ker(N_G)/im(D_g). For
z∈Z³(G,A), write ν_g(z)=Σ_{h∈G}z(g,h,g)∈ker(N_G), and q_g:ker(N_G)→Q_g(A) for quotient
projection. For z∈Z³(G,A), the descended map F_g:H³(G,A)→Q_g(A) satisfies
F_g(π₃(z))=q_g(ν_g(z))=[Σ_hz(g,h,g)]. -/
@[simp]
theorem cyclicH3ToOddHomology_H3π
    (A : Rep k G) (g : G)
    (z : cocycles₃ A) :
    cyclicH3ToOddHomology A g (H3π A z) =
      cyclicOddHomologyπ A g (cyclicThreeCocycleInvariant A g z) := by
  exact cyclicOddComparisonQuotientMap_H3π A g z

/-- Let k be a commutative ring, G a finite abelian group, and A a k-linear G-representation, in
universe u. For g∈G put D_g=ρ(g)-id, N_G=Σ_{h∈G}ρ(h), and Q_g(A)=ker(N_G)/im(D_g). The linear
map F_g:H³(G,A)→Q_g(A) obtained by cyclic-invariant descent equals the underlying k-linear map
of the concrete odd short-complex homology comparison. Both maps use the same norm quotient and
class projection. -/
theorem cyclicH3ToOddHomology_eq_cyclicOddComparisonQuotientMap
    (A : Rep k G) (g : G) :
    cyclicH3ToOddHomology A g =
      (cyclicOddComparisonQuotientMap A g).hom :=
  rfl

/-- Let k be a commutative ring, G a finite abelian group, and A a k-linear G-representation, in
universe u. For g∈G put D_g=ρ(g)-id, N_G=Σ_{h∈G}ρ(h), and Q_g(A)=ker(N_G)/im(D_g). Assume g
generates G, so every element belongs to its subgroup of powers. The periodic-resolution
cohomology comparison in degree three, followed by its concrete quotient identification, gives a
k-linear equivalence E_g:H³(G,A)≃Q_g(A). It uses the periodic resolution of the trivial
k-representation. -/
noncomputable def cyclicH3OddLinearEquiv
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    H3 A ≃ₗ[k] cyclicOddQuotient A g :=
  ((Rep.FiniteCyclicGroup.groupCohomologyIsoOdd
    A g hg 3 (by exact ⟨1, rfl⟩)) ≪≫
      (Rep.FiniteCyclicGroup.subCompNormHom A g).moduleCatHomologyIso).toLinearEquiv

/-- Let k be a commutative ring, G a finite abelian group, and A a k-linear G-representation, in
universe u. For g∈G put D_g=ρ(g)-id, N_G=Σ_{h∈G}ρ(h), and Q_g(A)=ker(N_G)/im(D_g). Assume g
generates G, so every element belongs to its subgroup of powers. Let F_g:H³(G,A)→Q_g(A) be
cyclic-invariant descent and E_g:H³(G,A)≃Q_g(A) the periodic-resolution equivalence. The
comparison property is the equality F_g=E_g.toLinearMap. -/
def CyclicH3ComparisonCompatible
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) : Prop :=
  cyclicH3ToOddHomology A g =
    (cyclicH3OddLinearEquiv A g hg).toLinearMap

/-- Let k be a commutative ring, G a finite abelian group, and A a k-linear G-representation, in
universe u. For g∈G put D_g=ρ(g)-id, N_G=Σ_{h∈G}ρ(h), and Q_g(A)=ker(N_G)/im(D_g). Assume g
generates G, so every element belongs to its subgroup of powers. For z∈Z³(G,A), write
ν_g(z)=Σ_{h∈G}z(g,h,g)∈ker(N_G), and q_g:ker(N_G)→Q_g(A) for quotient projection. For the
invariant descent F_g and periodic-resolution equivalence E_g, the comparison property
F_g=E_g.toLinearMap holds if and only if E_g(π₃(z))=q_g(ν_g(z)) for every z∈Z³(G,A).
Surjectivity of π₃ makes the cocycle formulas determine the whole maps. -/
theorem cyclicH3ComparisonCompatible_iff
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    CyclicH3ComparisonCompatible A g hg ↔
      ∀ z : cocycles₃ A,
        cyclicH3OddLinearEquiv A g hg (H3π A z) =
          cyclicOddHomologyπ A g
            (cyclicThreeCocycleInvariant A g z) := by
  constructor
  · intro h z
    change (cyclicH3OddLinearEquiv A g hg).toLinearMap (H3π A z) = _
    rw [← h]
    exact cyclicH3ToOddHomology_H3π A g z
  · intro h
    apply LinearMap.ext
    intro c
    refine H3_induction_on c ?_
    intro z
    rw [cyclicH3ToOddHomology_H3π]
    exact (h z).symm

/-- Let k be a commutative ring, G a finite abelian group, and A a k-linear G-representation, in
universe u. For g∈G put D_g=ρ(g)-id, N_G=Σ_{h∈G}ρ(h), and Q_g(A)=ker(N_G)/im(D_g). For
z∈Z³(G,A), write ν_g(z)=Σ_{h∈G}z(g,h,g)∈ker(N_G), and q_g:ker(N_G)→Q_g(A) for quotient
projection. For x,y∈Z³(G,A), if π₃(x)=π₃(y), then ν_g(x)-ν_g(y)∈im(D_g) in A. Thus the two
norm-kernel sums have the same class in Q_g(A). -/
theorem cyclicThreeCocycleInvariant_sub_mem_range
    (A : Rep k G) (g : G) (x y : cocycles₃ A)
    (hxy : H3π A x = H3π A y) :
    (cyclicThreeCocycleInvariant A g x : A) -
        cyclicThreeCocycleInvariant A g y ∈
      LinearMap.range
        (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap := by
  obtain ⟨t, ht⟩ := (H3π_eq_iff x y).mp hxy
  refine ⟨∑ h : G, t (h, g), ?_⟩
  change A.ρ g (∑ h : G, t (h, g)) - ∑ h : G, t (h, g) = _
  rw [← cyclicSumThree_d₂₃ A g t, ht]
  rw [map_sub]
  rw [cyclicThreeCocycleInvariant_coe, cyclicThreeCocycleInvariant_coe]

/-- Let k be a commutative ring, G a finite abelian group, A,B k-linear representations in universe
u, and g∈G. For x∈Z¹(G,A), y∈Z²(G,B), the cup cocycle c(a,h,i)=x(a)⊗ρ_B(a)y(h,i) has cyclic sum
Σ_hc(g,h,g)=Σ_hx(g)⊗ρ_B(g)y(h,g) in A⊗_k B. -/
theorem cyclicSumThree_cupCocycleOneTwo
    (A B : Rep k G) (g : G)
    (x : cocycles₁ A) (y : cocycles₂ B) :
    cyclicSumThree (A ⊗ B) g
        (cupCocycleOneTwo A B x y) =
      ∑ h : G, x g ⊗ₜ[k] B.ρ g (y (h, g)) :=
  rfl

/-- Let k be a commutative ring, G a finite abelian group, A,B k-linear representations in universe
u, and g∈G. For x∈Z¹(G,A), y∈Z²(G,B), the invariant of their cup is
ν_g(x∪y)=Σ_hx(g)⊗ρ_B(g)y(h,g), regarded in the kernel of the representation norm on A⊗_k B. -/
noncomputable def cyclicCupOneTwoInvariant
    (A B : Rep k G) (g : G)
    (x : cocycles₁ A) (y : cocycles₂ B) :
    LinearMap.ker (A ⊗ B).norm.asHom.hom.toLinearMap :=
  cyclicThreeCocycleInvariant (A ⊗ B) g
    (cupCocycleOneTwo A B x y)

@[simp]
theorem cyclicCupOneTwoInvariant_coe
    (A B : Rep k G) (g : G)
    (x : cocycles₁ A) (y : cocycles₂ B) :
    (cyclicCupOneTwoInvariant A B g x y).1 =
      ∑ h : G, x g ⊗ₜ[k] B.ρ g (y (h, g)) := by
  rw [cyclicCupOneTwoInvariant, cyclicThreeCocycleInvariant_coe,
    cyclicSumThree_cupCocycleOneTwo]

/-- Let k be a commutative ring, G a finite abelian group, A,B k-linear representations in universe
u, and g∈G. For x∈Z¹(G,A), y∈Z²(G,B), F_g([x∪y]) is the class of Σ_hx(g)⊗ρ_B(g)y(h,g) in
ker(N_{A⊗B})/im(ρ_{A⊗B}(g)-id). The class is formed from the explicit cup cocycle. -/
theorem cyclicH3ToOddHomology_cupOneTwo
    (A B : Rep k G) (g : G)
    (x : cocycles₁ A) (y : cocycles₂ B) :
    cyclicH3ToOddHomology (A ⊗ B) g
        (H3π (A ⊗ B) (cupCocycleOneTwo A B x y)) =
      cyclicOddHomologyπ (A ⊗ B) g
        (cyclicCupOneTwoInvariant A B g x y) :=
  cyclicH3ToOddHomology_H3π (A ⊗ B) g _

/-- Let k be a commutative ring, G a finite abelian group, A,B,C k-linear representations in
universe u, and g∈G. For x∈Z¹(G,A), y∈Z¹(G,B), z∈Z¹(G,C), the cyclic sum of x∪(y∪z) is
Σ_hx(g)⊗ρ_{B⊗C}(g)(y(h)⊗ρ_C(h)z(g)) in A⊗(B⊗C). -/
theorem cyclicSumThree_nestedCupOneOne
    (A B C : Rep k G) (g : G)
    (x : cocycles₁ A) (y : cocycles₁ B) (z : cocycles₁ C) :
    cyclicSumThree (A ⊗ (B ⊗ C)) g
        (cupCocycleOneTwo A (B ⊗ C) x
          (cupCocycleOneOne B C y z)) =
      ∑ h : G, x g ⊗ₜ[k]
        (B ⊗ C).ρ g (y h ⊗ₜ[k] C.ρ h (z g)) :=
  rfl

/-- Let k be a commutative ring, G a finite abelian group, A,B,C k-linear representations in
universe u, and g∈G. For one-cocycles x,y,z, the vector
ν_g(x∪(y∪z))=Σ_hx(g)⊗ρ_{B⊗C}(g)(y(h)⊗ρ_C(h)z(g)) lies in the kernel of the representation norm
on A⊗(B⊗C). -/
noncomputable def cyclicNestedCupOneOneInvariant
    (A B C : Rep k G) (g : G)
    (x : cocycles₁ A) (y : cocycles₁ B) (z : cocycles₁ C) :
    LinearMap.ker (A ⊗ (B ⊗ C)).norm.asHom.hom.toLinearMap :=
  cyclicThreeCocycleInvariant (A ⊗ (B ⊗ C)) g
    (cupCocycleOneTwo A (B ⊗ C) x
      (cupCocycleOneOne B C y z))

@[simp]
theorem cyclicNestedCupOneOneInvariant_coe
    (A B C : Rep k G) (g : G)
    (x : cocycles₁ A) (y : cocycles₁ B) (z : cocycles₁ C) :
    (cyclicNestedCupOneOneInvariant A B C g x y z).1 =
      ∑ h : G, x g ⊗ₜ[k]
        (B ⊗ C).ρ g (y h ⊗ₜ[k] C.ρ h (z g)) := by
  rw [cyclicNestedCupOneOneInvariant,
    cyclicThreeCocycleInvariant_coe,
    cyclicSumThree_nestedCupOneOne]

/-- Let k be a commutative ring, G a finite abelian group, A,B,C k-linear representations in
universe u, and g∈G. For one-cocycles x,y,z, the descended map F_g sends [x∪(y∪z)] to the
quotient class of Σ_hx(g)⊗ρ_{B⊗C}(g)(y(h)⊗ρ_C(h)z(g)) modulo im(ρ_{A⊗(B⊗C)}(g)-id) in the norm
kernel. -/
theorem cyclicH3ToOddHomology_nestedCupOneOne
    (A B C : Rep k G) (g : G)
    (x : cocycles₁ A) (y : cocycles₁ B) (z : cocycles₁ C) :
    cyclicH3ToOddHomology (A ⊗ (B ⊗ C)) g
        (H3π (A ⊗ (B ⊗ C))
          (cupCocycleOneTwo A (B ⊗ C) x
            (cupCocycleOneOne B C y z))) =
      cyclicOddHomologyπ (A ⊗ (B ⊗ C)) g
        (cyclicNestedCupOneOneInvariant A B C g x y z) :=
  cyclicH3ToOddHomology_H3π (A ⊗ (B ⊗ C)) g _

/-- Let k be a commutative ring, G a finite abelian group generated by g, and A,B,C k-linear
representations in universe u. Assume the periodic-resolution equivalence E_g for D=A⊗(B⊗C)
equals the explicit invariant descent as a linear map. For one-cocycles x,y,z, E_g([x∪(y∪z)]) is
the class of Σ_hx(g)⊗ρ_{B⊗C}(g)(y(h)⊗ρ_C(h)z(g)) in ker(N_D)/im(ρ_D(g)-id). -/
theorem cyclicH3OddLinearEquiv_nestedCupOneOne_of_compatible
    (A B C : Rep k G) (g : G)
    (hg : ∀ a, a ∈ Subgroup.zpowers g)
    (hcompat : CyclicH3ComparisonCompatible (A ⊗ (B ⊗ C)) g hg)
    (x : cocycles₁ A) (y : cocycles₁ B) (z : cocycles₁ C) :
    cyclicH3OddLinearEquiv (A ⊗ (B ⊗ C)) g hg
        (H3π (A ⊗ (B ⊗ C))
          (cupCocycleOneTwo A (B ⊗ C) x
            (cupCocycleOneOne B C y z))) =
      cyclicOddHomologyπ (A ⊗ (B ⊗ C)) g
        (cyclicNestedCupOneOneInvariant A B C g x y z) :=
  (cyclicH3ComparisonCompatible_iff
    (A ⊗ (B ⊗ C)) g hg).mp hcompat _

end groupCohomology
