/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Instances.AddCircle.Defs

import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section

namespace MathlibExt.GroupTheory.SU2Longitude

/-!
# The fixed diagonal longitude subgroup of `SU₂`

The subgroup of diagonal rotations in `SU₂` is isomorphic to the circle
group `ℝ / 2πℤ`. The real-angle homomorphism
`θ ↦ diag (exp (iθ), exp (-iθ))` has period `2π` and factors through
`AddCircle (2 * Real.pi)`. The resulting quotient map is injective because
equal diagonal rotations have angles differing by an integral multiple of
`2π`, and surjective by the definition of this diagonal subgroup.

This is a supporting result for the fixed equator point `i`. ATLAS
`v1/Atlas/AlgebraNotes`, targets entry 67 states the longitude isomorphism
for every equator point `x`; that general quantifier and its conjugation
argument are not formalized here. The fixed-point v1 statement
`SimpleGroups.longitude_iso` in `v1/Atlas/AlgebraNotes/code/SimpleGroups.lean`
is left unproved there. The independent proof below factors the angle
homomorphism through the quotient and uses
`Complex.exp_eq_exp_iff_exists_int` to identify equal angle classes.
-/

open Matrix

/-- **Diagonal rotation.** For a real number $\theta$, the diagonal rotation through $\theta$ is
the $2 \times 2$ complex diagonal matrix $\operatorname{diag}(e^{i\theta}, e^{-i\theta})$. -/
noncomputable def diagRotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (↑θ * Complex.I), 0; 0, Complex.exp (-(↑θ * Complex.I))]

/-- **Diagonal rotations as diagonal matrices.** For every real number $\theta$, the diagonal
rotation through $\theta$ is the diagonal matrix whose diagonal entries are $e^{i\theta}$ and
$e^{-i\theta}$, in that order. -/
theorem diagRotation_eq_diagonal (θ : ℝ) : diagRotation θ =
    Matrix.diagonal ![Complex.exp (↑θ * Complex.I),
      Complex.exp (-(↑θ * Complex.I))] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagRotation, Matrix.diagonal]

theorem diagRotation_add (θ₁ θ₂ : ℝ) :
    diagRotation θ₁ * diagRotation θ₂ = diagRotation (θ₁ + θ₂) := by
  rw [diagRotation_eq_diagonal, diagRotation_eq_diagonal, diagRotation_eq_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [← Complex.exp_add]
  · congr 1; ring
  · congr 1; ring

theorem diagRotation_zero : diagRotation 0 = 1 := by
  simp only [diagRotation]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **Conjugate transpose of a diagonal rotation.** For every real number $\theta$, the conjugate
transpose of the diagonal rotation through $\theta$ is the diagonal rotation through $-\theta$. -/
theorem star_diagRotation (θ : ℝ) : star (diagRotation θ) = diagRotation (-θ) := by
  rw [diagRotation_eq_diagonal, diagRotation_eq_diagonal, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  fin_cases i <;> simp [← Complex.exp_conj]

/-- **Diagonal rotations lie in $\mathrm{SU}(2)$.** For every real number $\theta$, the
diagonal rotation through $\theta$ is a $2 \times 2$ complex matrix that is unitary and has
determinant $1$, that is, it lies in $\mathrm{SU}(2)$. -/
theorem diagRotation_mem_specialUnitaryGroup (θ : ℝ) :
    diagRotation θ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', star_diagRotation, diagRotation_add]
    simp [diagRotation_zero]
  · rw [Matrix.det_fin_two]
    simp [diagRotation, ← Complex.exp_add]

/-- **Diagonal rotation through a multiple of $2\pi$.** For every integer $n$, the diagonal
rotation through $2\pi n$ is the $2 \times 2$ identity matrix. -/
theorem diagRotation_int_mul_two_pi (n : ℤ) : diagRotation (n * (2 * Real.pi)) = 1 := by
  rw [diagRotation_eq_diagonal]
  have h1 : Complex.exp (↑n * (2 * ↑Real.pi) * Complex.I) = 1 := by
    have h : ↑n * (2 * ↑Real.pi) * Complex.I = ↑n * (2 * ↑Real.pi * Complex.I) := by ring
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  have h2 : Complex.exp (-(↑n * (2 * ↑Real.pi) * Complex.I)) = 1 := by
    have h : -(↑n * (2 * ↑Real.pi) * Complex.I) = ↑(-n) * (2 * ↑Real.pi * Complex.I) := by
      push_cast; ring
    rw [h, Complex.exp_int_mul_two_pi_mul_I]
  rw [show (1 : Matrix (Fin 2) (Fin 2) ℂ) = Matrix.diagonal ![1, 1] from by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]]
  congr 1
  funext i
  fin_cases i <;> simp [h1, h2]

/-- **Diagonal rotations are $2\pi$-periodic.** For every real number $\theta$ and every integer
$n$, the diagonal rotation through $\theta + 2\pi n$ equals the diagonal rotation through
$\theta$. -/
theorem diagRotation_add_int_mul_two_pi (θ : ℝ) (n : ℤ) :
    diagRotation (θ + n * (2 * Real.pi)) = diagRotation θ := by
  rw [← diagRotation_add, diagRotation_int_mul_two_pi, mul_one]

/-- **Longitude subgroup.** The longitude subgroup of $\mathrm{SU}(2)$ is the subgroup of those
elements of $\mathrm{SU}(2)$ that are the diagonal rotation through $\theta$ for some real number
$\theta$.

It is the longitude $\mathrm{Long}_i$ at the equator point $i$. -/
def longitudeSubgroup : Subgroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) where
  carrier := {M | ∃ θ : ℝ, (M : Matrix (Fin 2) (Fin 2) ℂ) = diagRotation θ}
  mul_mem' := by
    intro a b ⟨θ₁, hθ₁⟩ ⟨θ₂, hθ₂⟩
    exact ⟨θ₁ + θ₂, by
      simp only [Submonoid.coe_mul, hθ₁, hθ₂, diagRotation_add]⟩
  one_mem' := ⟨0, diagRotation_zero.symm⟩
  inv_mem' := by
    intro a ⟨θ, hθ⟩
    refine ⟨-θ, ?_⟩
    have ha : ((a⁻¹ : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) = star (a : Matrix (Fin 2) (Fin 2) ℂ) := by
      rw [← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star]
    rw [ha, hθ, star_diagRotation]

/-- **Diagonal rotation as a longitude element.** For a real number $\theta$, the diagonal
rotation through $\theta$, regarded as an element of the longitude subgroup of
$\mathrm{SU}(2)$. -/
noncomputable def diagRotationToLongitude (θ : ℝ) : longitudeSubgroup :=
  ⟨⟨diagRotation θ, diagRotation_mem_specialUnitaryGroup θ⟩, ⟨θ, rfl⟩⟩

/-- **Longitude elements multiply by adding angles.** For real numbers $a$ and $b$, in the
longitude subgroup the product of the diagonal rotations through $a$ and through $b$ is the
diagonal rotation through $a + b$. -/
theorem diagRotationToLongitude_mul (a b : ℝ) :
    diagRotationToLongitude a * diagRotationToLongitude b =
      diagRotationToLongitude (a + b) :=
  Subtype.ext (Subtype.ext (diagRotation_add a b))

/-- **Equal rotation matrices give equal longitude elements.** For real numbers $a$ and $b$, if
the diagonal rotations through $a$ and through $b$ are equal as matrices, then the elements of
the longitude subgroup given by the diagonal rotations through $a$ and through $b$ are
equal. -/
theorem diagRotationToLongitude_eq_of_diagRotation_eq {a b : ℝ}
    (h : diagRotation a = diagRotation b) :
    diagRotationToLongitude a = diagRotationToLongitude b :=
  Subtype.ext (Subtype.ext h)

/-- **The angle homomorphism into the longitude subgroup.** The homomorphism from the additive
group $\mathbb{R}$ to the longitude subgroup, written additively, that sends a real number
$\theta$ to the diagonal rotation through $\theta$, regarded as an element of the longitude
subgroup. -/
noncomputable def diagRotationToLongitudeHom : ℝ →+ Additive longitudeSubgroup where
  toFun θ := Additive.ofMul (diagRotationToLongitude θ)
  map_zero' := by
    rw [show (0 : Additive longitudeSubgroup) = Additive.ofMul 1 from rfl]
    congr 1
    exact Subtype.ext (Subtype.ext diagRotation_zero)
  map_add' θ₁ θ₂ := by
    show Additive.ofMul (diagRotationToLongitude (θ₁ + θ₂)) =
      Additive.ofMul (diagRotationToLongitude θ₁ * diagRotationToLongitude θ₂)
    exact congrArg Additive.ofMul (diagRotationToLongitude_mul θ₁ θ₂).symm

/-- **Longitude map.** The longitude map is the group homomorphism from the circle group
$\mathbb{R}/2\pi\mathbb{Z}$, written multiplicatively, to the longitude subgroup of $\mathrm{SU}(2)$
that sends the class of a real number $\theta$ to the diagonal rotation through $\theta$, that is,
to $\cos\theta \cdot I + \sin\theta \cdot \operatorname{diag}(i, -i) =
\operatorname{diag}(e^{i\theta}, e^{-i\theta})$, where $I$ is the $2 \times 2$ identity matrix.
It is well defined because diagonal rotations are $2\pi$-periodic. -/
noncomputable def longitudeMap :
    Multiplicative (AddCircle (2 * Real.pi)) →* longitudeSubgroup :=
  AddMonoidHom.toMultiplicative
    (QuotientAddGroup.lift (AddSubgroup.zmultiples (2 * Real.pi))
      diagRotationToLongitudeHom (by
        intro a ha
        obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp ha
        show Additive.ofMul (diagRotationToLongitude a) = 0
        rw [← hn]
        have hdiag : diagRotation (n • (2 * Real.pi)) = 1 := by
          rw [zsmul_eq_mul]
          exact diagRotation_int_mul_two_pi n
        rw [show (0 : Additive longitudeSubgroup) = Additive.ofMul 1 from rfl]
        congr 1
        exact Subtype.ext (Subtype.ext hdiag)))

/-- **The longitude map on the class of an angle.** For every real number $\theta$, the longitude
map sends the class of $\theta$ in $\mathbb{R}/2\pi\mathbb{Z}$ to the diagonal rotation through
$\theta$, regarded as an element of the longitude subgroup. -/
theorem longitudeMap_apply_ofAdd_mk (θ : ℝ) :
    longitudeMap (Multiplicative.ofAdd (↑θ : AddCircle (2 * Real.pi))) =
      diagRotationToLongitude θ := by
  show Additive.toMul (QuotientAddGroup.lift (AddSubgroup.zmultiples (2 * Real.pi))
      diagRotationToLongitudeHom _ (↑θ : AddCircle (2 * Real.pi))) =
    diagRotationToLongitude θ
  rw [QuotientAddGroup.lift_mk]
  rfl

/-- **When two diagonal rotations are equal.** For real numbers $a$ and $b$, the diagonal
rotations through $a$ and through $b$ are equal if and only if $a = b + 2\pi n$ for some
integer $n$. -/
theorem diagRotation_eq_diagRotation_iff (a b : ℝ) :
    diagRotation a = diagRotation b ↔ ∃ n : ℤ, a = b + n * (2 * Real.pi) := by
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    obtain ⟨n, hn⟩ :=
      Complex.exp_eq_exp_iff_exists_int.mp (by simpa [diagRotation] using h00)
    refine ⟨n, ?_⟩
    have hn' : (↑a : ℂ) = ↑b + ↑n * (2 * ↑Real.pi) := by
      apply mul_right_cancel₀ Complex.I_ne_zero
      calc (↑a : ℂ) * Complex.I
          = ↑b * Complex.I + ↑n * (2 * ↑Real.pi * Complex.I) := hn
        _ = (↑b + ↑n * (2 * ↑Real.pi)) * Complex.I := by ring
    have hn'' : (↑a : ℂ) = ↑(b + ↑n * (2 * Real.pi)) := by
      push_cast
      exact hn'
    exact Complex.ofReal_inj.mp hn''
  · rintro ⟨n, rfl⟩
    exact diagRotation_add_int_mul_two_pi b n

/-- **Every point of $\mathbb{R}/2\pi\mathbb{Z}$ comes from a real angle.** Every element $x$ of
the circle group $\mathbb{R}/2\pi\mathbb{Z}$, written multiplicatively, is the class of some real
number $a$. -/
theorem exists_ofAdd_mk_eq (x : Multiplicative (AddCircle (2 * Real.pi))) :
    ∃ a : ℝ, x = Multiplicative.ofAdd (↑a : AddCircle (2 * Real.pi)) := by
  obtain ⟨a, ha⟩ := Quotient.exists_rep (Multiplicative.toAdd x)
  refine ⟨a, ?_⟩
  show Multiplicative.ofAdd (Multiplicative.toAdd x) =
    Multiplicative.ofAdd (↑a : AddCircle (2 * Real.pi))
  congr 1
  exact ha.symm

/-- **The longitude map is injective.** The longitude map from the circle group
$\mathbb{R}/2\pi\mathbb{Z}$, written multiplicatively, to the longitude subgroup of $\mathrm{SU}(2)$
is injective.

The angle class is recovered from the diagonal rotation via the complex exponential. -/
theorem longitudeMap_injective : Function.Injective longitudeMap := by
  intro x y h
  obtain ⟨a, ha⟩ := exists_ofAdd_mk_eq x
  obtain ⟨b, hb⟩ := exists_ofAdd_mk_eq y
  rw [ha, hb, longitudeMap_apply_ofAdd_mk, longitudeMap_apply_ofAdd_mk] at h
  have hmat : diagRotation a = diagRotation b := congrArg Subtype.val (congrArg Subtype.val h)
  obtain ⟨n, hn⟩ := (diagRotation_eq_diagRotation_iff a b).mp hmat
  rw [ha, hb]
  congr 1
  rw [QuotientAddGroup.eq, AddSubgroup.mem_zmultiples_iff]
  refine ⟨-n, ?_⟩
  rw [hn]
  simp [zsmul_eq_mul]

/-- **The longitude map is surjective.** The longitude map from the circle group
$\mathbb{R}/2\pi\mathbb{Z}$, written multiplicatively, to the longitude subgroup of $\mathrm{SU}(2)$
is surjective: every element of the longitude subgroup is the image of some class. -/
theorem longitudeMap_surjective : Function.Surjective longitudeMap := by
  rintro ⟨M, hM⟩
  obtain ⟨θ, hθ⟩ := hM
  refine ⟨Multiplicative.ofAdd (↑θ : AddCircle (2 * Real.pi)), ?_⟩
  rw [longitudeMap_apply_ofAdd_mk]
  exact Subtype.ext (Subtype.ext hθ).symm

/-- **The longitude map is bijective.** The longitude map from the circle group
$\mathbb{R}/2\pi\mathbb{Z}$, written multiplicatively, to the longitude subgroup of $\mathrm{SU}(2)$
is bijective. -/
theorem longitudeMap_bijective : Function.Bijective longitudeMap :=
  ⟨longitudeMap_injective, longitudeMap_surjective⟩

/-- **Isomorphism of the circle group with the longitude subgroup.** The group isomorphism from
the circle group $\mathbb{R}/2\pi\mathbb{Z}$, written multiplicatively, onto the longitude
subgroup of $\mathrm{SU}(2)$ given by the longitude map, which sends the class of a real number
$\theta$ to the diagonal rotation through $\theta$. -/
noncomputable def longitudeMulEquiv :
    Multiplicative (AddCircle (2 * Real.pi)) ≃* longitudeSubgroup :=
  MulEquiv.ofBijective longitudeMap longitudeMap_bijective

end MathlibExt.GroupTheory.SU2Longitude
