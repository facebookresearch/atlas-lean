/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Tactic.Ring

/-!
# Coordinate rings of the expanded degeneration charts

For chart `i` of the small resolution of `xy = t₀ … tₙ`, the independent
coordinates are `uᵢ`, `vᵢ`, and the parameters other than `tᵢ`.
The actual base map is `tᵢ = uᵢ vᵢ`; its contraction is
`x = (∏ j < i, tⱼ) uᵢ`, `y = vᵢ (∏ j > i, tⱼ)`.

The coefficient algebra is arbitrary. In particular, the construction
retains its nilpotents and does not replace it by functions on field points.
Smooth finite-presentation coefficient charts are qualified separately by
the geometric construction interface.

Source: Jun Li, *Stable morphisms to singular schemes and relative stable
morphisms*, arXiv:math/0009097v1, equation (1.7), Lemma 1.2(i)–(ii).
The adjacent transition is normalized against these base maps, correcting
the divided factors printed in Lemma 1.2(iii).
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DegenerationParameterModels

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

universe u
variable (B : Type u) [CommRing B]

abbrev ParameterRing (n : ℕ) := MvPolynomial (Fin (n + 1)) B
abbrev NodeRing := MvPolynomial (Fin 2) B
abbrev ChartVariable {n : ℕ} (i : Fin (n + 1)) :=
  Fin 2 ⊕ {j : Fin (n + 1) // j ≠ i}
abbrev ChartRing {n : ℕ} (i : Fin (n + 1)) := MvPolynomial (ChartVariable i) B

variable {B} {n : ℕ}

def uCoordinate (i : Fin (n + 1)) : ChartRing B i := MvPolynomial.X (.inl 0)
def vCoordinate (i : Fin (n + 1)) : ChartRing B i := MvPolynomial.X (.inl 1)

def parameterValue (i j : Fin (n + 1)) : ChartRing B i :=
  if h : j = i then uCoordinate i * vCoordinate i
  else MvPolynomial.X (.inr ⟨j, h⟩)

@[simp] theorem parameterValue_self (i : Fin (n + 1)) :
    parameterValue (B := B) i i = uCoordinate i * vCoordinate i := by
  simp [parameterValue]

def parameterHom (i : Fin (n + 1)) : ParameterRing B n →ₐ[B] ChartRing B i :=
  MvPolynomial.aeval (parameterValue i)

def earlier (i : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun j => j < i

def later (i : Fin (n + 1)) : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun j => i < j

def contractionX (i : Fin (n + 1)) : ChartRing B i :=
  (∏ j ∈ earlier i, parameterValue i j) * uCoordinate i

def contractionY (i : Fin (n + 1)) : ChartRing B i :=
  vCoordinate i * ∏ j ∈ later i, parameterValue i j

private theorem ordered_product {M : Type*} [CommMonoid M]
    (f : Fin (n + 1) → M) (i : Fin (n + 1)) :
    (∏ j ∈ earlier i, f j) * f i * (∏ j ∈ later i, f j) = ∏ j, f j := by
  have hd : Disjoint (earlier i) (later i) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    exact lt_asymm (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2
  have he : Finset.univ.erase i = earlier i ∪ later i := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union,
      earlier, later, Finset.mem_filter, true_and]
    constructor
    · intro h
      rcases lt_trichotomy j i with h' | h' | h'
      · exact Or.inl h'
      · exact (h h').elim
      · exact Or.inr h'
    · rintro (h | h)
      · exact ne_of_lt h
      · exact ne_of_gt h
  calc
    (∏ j ∈ earlier i, f j) * f i * (∏ j ∈ later i, f j) =
        (∏ j ∈ earlier i ∪ later i, f j) * f i := by
          rw [Finset.prod_union hd]
          simp only [mul_assoc, mul_comm (f i)]
    _ = (∏ j ∈ Finset.univ.erase i, f j) * f i := by rw [he]
    _ = ∏ j, f j := Finset.prod_erase_mul _ _ (by simp)

theorem contraction_product (i : Fin (n + 1)) :
    contractionX (B := B) i * contractionY i = ∏ j, parameterValue i j := by
  rw [← ordered_product (parameterValue (B := B) i) i, parameterValue_self]
  dsimp [contractionX, contractionY]
  ring

def contractionHom (i : Fin (n + 1)) : NodeRing B →ₐ[B] ChartRing B i :=
  MvPolynomial.aeval (fun j => if j = 0 then contractionX i else contractionY i)

def productHom : Polynomial B →ₐ[B] ParameterRing B n :=
  Polynomial.aeval (∏ j : Fin (n + 1), MvPolynomial.X j)

def smoothingHom : Polynomial B →ₐ[B] NodeRing B :=
  Polynomial.aeval (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2))

theorem contraction_over_base (i : Fin (n + 1)) :
    (contractionHom (B := B) i).comp smoothingHom =
      (parameterHom i).comp (productHom (n := n)) := by
  ext1
  simp [contractionHom, smoothingHom, parameterHom, productHom,
    contraction_product, map_prod]

abbrev parameterScheme (n : ℕ) := Spec (CommRingCat.of (ParameterRing B n))
abbrev nodeScheme := Spec (CommRingCat.of (NodeRing B))
abbrev chartScheme (i : Fin (n + 1)) := Spec (CommRingCat.of (ChartRing B i))
abbrev smoothingBase := Spec (CommRingCat.of (Polynomial B))

def chartParameter (i : Fin (n + 1)) : chartScheme (B := B) i ⟶ parameterScheme (B := B) n :=
  Spec.map (CommRingCat.ofHom (parameterHom i).toRingHom)

def chartContraction (i : Fin (n + 1)) : chartScheme (B := B) i ⟶ nodeScheme (B := B) :=
  Spec.map (CommRingCat.ofHom (contractionHom i).toRingHom)

def parameterProduct : parameterScheme (B := B) n ⟶ smoothingBase (B := B) :=
  Spec.map (CommRingCat.ofHom (productHom (B := B) (n := n)).toRingHom)

def nodeSmoothing : nodeScheme (B := B) ⟶ smoothingBase (B := B) :=
  Spec.map (CommRingCat.ofHom (smoothingHom (B := B)).toRingHom)

theorem contraction_square (i : Fin (n + 1)) :
    chartContraction (B := B) i ≫ nodeSmoothing (B := B) =
      chartParameter i ≫ parameterProduct := by
  simp only [chartContraction, nodeSmoothing, chartParameter, parameterProduct,
    ← Spec.map_comp]
  congr 1
  exact congrArg (fun f : Polynomial B →ₐ[B] ChartRing B i =>
    CommRingCat.ofHom f.toRingHom) (contraction_over_base (B := B) i)

end MathlibExt.AlgebraicGeometry.DegenerationParameterModels
