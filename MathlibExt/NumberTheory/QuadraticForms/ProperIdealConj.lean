/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import MathlibExt.NumberTheory.QuadraticForms.ProperIdealRootLattice
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# A proper ideal times its conjugate

Let $a, b, c \in \mathbb{Z}$ with $\gcd(a, b, c) = 1$, $a > 0$ and $b^2 - 4ac < 0$, let $\tau$ be
a root of $a\tau^2 + b\tau + c = 0$, and let $\alpha \neq 0$. For the lattice
$\mathfrak{a} = \alpha[1, \tau]$ and the order $\mathcal{O} = [1, a\tau]$ this file proves

* `BinaryQuadraticForm.span_mul_map_conj_span`: $\mathfrak{a}\bar{\mathfrak{a}} =
  \frac{|\alpha|^2}{a}\mathcal{O}$;
* `BinaryQuadraticForm.relIndex_span_pair_eq`: if $\mathfrak{a} \subseteq \mathcal{O}$, then
  $[\mathcal{O} : \mathfrak{a}] = |\alpha|^2 / a$, a positive integer;
* `PeriodPair.lattice_mul_map_conj_eq_relIndex_smul`: for a period lattice $L = \mathfrak{a}$
  contained in $\mathcal{O}$, $L\bar{L} = N\mathcal{O}$ with $N = [\mathcal{O} : L] \neq 0$, and
  $L \cdot N^{-1}\bar{L} = \mathcal{O}$;
* `PeriodPair.lattice_mul_map_conj_eq_relIndex_smul_of_isProperIdeal`: the same for every proper
  ideal $L \subseteq \mathcal{O}$ of an order $\mathcal{O} = \mathbb{Z} + \mathbb{Z}\omega$.

Complex conjugation of a lattice is its image under the $\mathbb{Z}$-linear map
`(starRingEnd ℂ).toIntAlgHom.toLinearMap`, and products of lattices are products of
$\mathbb{Z}$-submodules of the $\mathbb{Z}$-algebra $\mathbb{C}$.

The source is Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare,
Fall 2025, Lecture 17, Theorem 17.10 and its proof.
-/

@[expose] public section

open Complex
open scoped Pointwise ComplexConjugate

namespace BinaryQuadraticForm

/-- The complex conjugate of the lattice spanned by two complex numbers is spanned by their
conjugates. -/
private theorem map_conj_span_pair (x y : ℂ) :
    (Submodule.span ℤ {x, y}).map (starRingEnd ℂ).toIntAlgHom.toLinearMap =
      Submodule.span ℤ {conj x, conj y} := by
  rw [Submodule.map_span, Set.image_pair]
  rfl

/-- Scaling a `ℤ`-submodule of `ℂ` by an integer `n` is scaling it by the complex number `n`. -/
private theorem int_smul_submodule_eq (n : ℤ) (S : Submodule ℤ ℂ) : n • S = (n : ℂ) • S := by
  ext x
  simp only [Submodule.mem_smul_pointwise_iff_exists, zsmul_eq_mul, smul_eq_mul]

private theorem bezout_three {a b c : ℤ} (hprim : Int.gcd (Int.gcd a b : ℤ) c = 1) :
    ∃ s₁ s₂ s₃ : ℤ, a * s₁ + b * s₂ + c * s₃ = 1 := by
  have h1 := Int.gcd_eq_gcd_ab (Int.gcd a b : ℤ) c
  have h2 := Int.gcd_eq_gcd_ab a b
  rw [hprim] at h1
  refine ⟨a.gcdA b * (Int.gcd a b : ℤ).gcdA c, a.gcdB b * (Int.gcd a b : ℤ).gcdA c,
    (Int.gcd a b : ℤ).gcdB c, ?_⟩
  have h1' : (1 : ℤ) = (Int.gcd a b : ℤ) * (Int.gcd a b : ℤ).gcdA c +
      c * (Int.gcd a b : ℤ).gcdB c := by exact_mod_cast h1
  linear_combination -h1' - ((Int.gcd a b : ℤ).gcdA c) * h2

variable {a b c : ℤ} {τ α : ℂ}

/-- **A lattice times its conjugate.** Let $a, b, c \in \mathbb{Z}$ with $\gcd(a, b, c) = 1$,
$a > 0$ and $b^2 - 4ac < 0$, let $\tau \in \mathbb{C}$ satisfy $a\tau^2 + b\tau + c = 0$, and let
$\alpha \in \mathbb{C}$. Then, as $\mathbb{Z}$-submodules of $\mathbb{C}$,
$$(\mathbb{Z}\alpha + \mathbb{Z}\alpha\tau) \cdot \overline{(\mathbb{Z}\alpha +
\mathbb{Z}\alpha\tau)} = \frac{|\alpha|^2}{a}\,(\mathbb{Z} + \mathbb{Z}a\tau),$$
where the conjugate lattice is the image under complex conjugation.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare, Fall
2025, Lecture 17, proof of Theorem 17.10, the computation
$\mathfrak{a}\bar{\mathfrak{a}} = N(\alpha)[1, \tau, \bar\tau, \tau\bar\tau] =
\frac{N(\alpha)}{a}[a, a\tau, -b, c] = \frac{N(\alpha)}{a}[1, a\tau]$; the generator-by-generator
verification, with Bézout coefficients for $\gcd(a, b, c) = 1$, is written out here. -/
theorem span_mul_map_conj_span (hprim : Int.gcd (Int.gcd a b : ℤ) c = 1) (ha : 0 < a)
    (hD : discrim a b c < 0) (hτ : (a : ℂ) * τ ^ 2 + b * τ + c = 0) :
    Submodule.span ℤ {α, α * τ} *
        (Submodule.span ℤ {α, α * τ}).map (starRingEnd ℂ).toIntAlgHom.toLinearMap =
      ((normSq α / a : ℝ) : ℂ) • Submodule.span ℤ {(1 : ℂ), a * τ} := by
  have hτ0 := im_ne_zero_of_root hD hτ
  have hadd := mul_root_add_conj hτ0 hτ
  have hmul := mul_root_mul_conj hτ0 hτ
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  set r : ℂ := ((normSq α / a : ℝ) : ℂ) with hr
  have hra : r * a = α * conj α := by
    rw [mul_conj, hr]
    push_cast
    field_simp
  rw [map_conj_span_pair, Submodule.span_mul_span, Submodule.smul_span]
  set P := Submodule.span ℤ (r • ({(1 : ℂ), a * τ} : Set ℂ))
  have hu : r ∈ P := Submodule.subset_span ⟨1, by simp, by simp⟩
  have hv : r * (a * τ) ∈ P := Submodule.subset_span ⟨a * τ, by simp, by simp⟩
  set Q := Submodule.span ℤ (({α, α * τ} : Set ℂ) * {conj α, conj (α * τ)})
  have mem : ∀ x ∈ ({α, α * τ} : Set ℂ), ∀ y ∈ ({conj α, conj (α * τ)} : Set ℂ), x * y ∈ Q :=
    fun x hx y hy ↦ Submodule.subset_span (Set.mul_mem_mul hx hy)
  have p₁ := mem α (by simp) (conj α) (by simp)
  have p₂ := mem α (by simp) (conj (α * τ)) (by simp)
  have p₃ := mem (α * τ) (by simp) (conj α) (by simp)
  have p₄ := mem (α * τ) (by simp) (conj (α * τ)) (by simp)
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    dsimp only
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
    · have e : α * conj α = a • r := by rw [zsmul_eq_mul]; linear_combination -hra
      rw [e]
      exact P.smul_mem _ hu
    · have e : α * conj (α * τ) = (-b) • r - r * (a * τ) := by
        rw [zsmul_eq_mul, map_mul]
        push_cast
        linear_combination (-conj τ) * hra + r * hadd
      rw [e]
      exact P.sub_mem (P.smul_mem _ hu) hv
    · have e : α * τ * conj α = r * (a * τ) := by linear_combination (-τ) * hra
      rw [e]
      exact hv
    · have e : α * τ * conj (α * τ) = c • r := by
        rw [zsmul_eq_mul, map_mul]
        linear_combination (-τ * conj τ) * hra + r * hmul
      rw [e]
      exact P.smul_mem _ hu
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    dsimp only
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · obtain ⟨s₁, s₂, s₃, hs⟩ := bezout_three hprim
      have hs' : (a : ℂ) * s₁ + b * s₂ + c * s₃ = 1 := by exact_mod_cast hs
      have e : r • (1 : ℂ) = s₁ • (α * conj α) + s₂ • (-(α * conj (α * τ) + α * τ * conj α)) +
          s₃ • (α * τ * conj (α * τ)) := by
        simp only [zsmul_eq_mul, smul_eq_mul, map_mul]
        linear_combination (-r) * hs' + (s₁ - s₂ * conj τ - s₂ * τ + s₃ * τ * conj τ) * hra +
          r * s₂ * hadd - r * s₃ * hmul
      rw [e]
      exact Q.add_mem (Q.add_mem (Q.smul_mem _ p₁) (Q.smul_mem _ (Q.neg_mem (Q.add_mem p₂ p₃))))
        (Q.smul_mem _ p₄)
    · have e : r • ((a : ℂ) * τ) = α * τ * conj α := by
        rw [smul_eq_mul]
        linear_combination τ * hra
      rw [e]
      exact p₃

private theorem linearIndependent_mul (hτ0 : τ.im ≠ 0) (hα : α ≠ 0) :
    LinearIndependent ℝ ![α, α * τ] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h' : α * ((s : ℂ) + t * τ) = 0 := by
    rw [real_smul, real_smul] at h
    linear_combination h
  have h'' : (s : ℂ) + t * τ = 0 := (mul_eq_zero.mp h').resolve_left hα
  exact LinearIndependent.pair_iff.mp (PeriodPair.ofTau τ hτ0).indep s t
    (by simpa [real_smul] using h'')

/-- **The norm of an integral lattice is its index.** Let $a, b, c \in \mathbb{Z}$ with $a > 0$ and
$b^2 - 4ac < 0$, let $\tau \in \mathbb{C}$ satisfy $a\tau^2 + b\tau + c = 0$, and let
$\alpha \in \mathbb{C}$ with $\alpha \neq 0$. If
$\mathfrak{a} = \mathbb{Z}\alpha + \mathbb{Z}\alpha\tau$ is contained in
$\mathcal{O} = \mathbb{Z} + \mathbb{Z}a\tau$, then the index of $\mathfrak{a}$ in $\mathcal{O}$
(as additive subgroups of $\mathbb{C}$) is $[\mathcal{O} : \mathfrak{a}] = |\alpha|^2 / a$, and it
is nonzero.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare, Fall
2025, Lecture 17, proof of Theorem 17.10, the computation $N(\mathfrak{a}) = [\mathcal{O} :
\mathfrak{a}] = N(\alpha)/a$. The argument written out here writes $\alpha = x + y\,a\tau$ and
$\alpha\tau = z + w\,a\tau$, computes the index as the determinant $|xw - yz|$, and compares
imaginary parts of $\bar\alpha \cdot \alpha\tau = |\alpha|^2\tau$ to get
$|\alpha|^2 = a(xw - yz)$. -/
theorem relIndex_span_pair_eq (ha : 0 < a) (hD : discrim a b c < 0)
    (hτ : (a : ℂ) * τ ^ 2 + b * τ + c = 0) (hα : α ≠ 0)
    (hle : Submodule.span ℤ {α, α * τ} ≤ Submodule.span ℤ {(1 : ℂ), a * τ}) :
    ((Submodule.span ℤ {α, α * τ}).toAddSubgroup.relIndex
        (Submodule.span ℤ {(1 : ℂ), a * τ}).toAddSubgroup : ℝ) = normSq α / a ∧
      (Submodule.span ℤ {α, α * τ}).toAddSubgroup.relIndex
        (Submodule.span ℤ {(1 : ℂ), a * τ}).toAddSubgroup ≠ 0 := by
  have hτ0 := im_ne_zero_of_root hD hτ
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have haτ : ((a : ℂ) * τ).im ≠ 0 := by
    simpa [ha.ne'] using hτ0
  set Λ := Submodule.span ℤ {α, α * τ} with hΛdef
  set 𝒪 := Submodule.span ℤ {(1 : ℂ), a * τ} with h𝒪def
  let LΛ : PeriodPair := ⟨α, α * τ, linearIndependent_mul hτ0 hα⟩
  let L𝒪 : PeriodPair := PeriodPair.ofTau (a * τ) haτ
  have hΛ : LΛ.lattice = Λ.toAddSubgroup.toIntSubmodule :=
    (Submodule.toAddSubgroup_toIntSubmodule Λ).symm
  have h𝒪 : L𝒪.lattice = 𝒪.toAddSubgroup.toIntSubmodule :=
    (Submodule.toAddSubgroup_toIntSubmodule 𝒪).symm
  let b₁ := LΛ.latticeBasis.map (LinearEquiv.ofEq _ _ hΛ)
  let b₂ := L𝒪.latticeBasis.map (LinearEquiv.ofEq _ _ h𝒪)
  have hb₁0 : (b₁ 0 : ℂ) = α := by
    rw [Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, PeriodPair.latticeBasis_zero]
  have hb₁1 : (b₁ 1 : ℂ) = α * τ := by
    rw [Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, PeriodPair.latticeBasis_one]
  have hb₂0 : (b₂ 0 : ℂ) = 1 := by
    rw [Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, PeriodPair.latticeBasis_zero]
    rfl
  have hb₂1 : (b₂ 1 : ℂ) = a * τ := by
    rw [Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, PeriodPair.latticeBasis_one]
    rfl
  obtain ⟨x, y, hxy⟩ := Submodule.mem_span_pair.mp (hle (Submodule.subset_span (by simp) : α ∈ Λ))
  obtain ⟨z, w, hzw⟩ :=
    Submodule.mem_span_pair.mp (hle (Submodule.subset_span (by simp) : α * τ ∈ Λ))
  have hle' : Λ.toAddSubgroup ≤ 𝒪.toAddSubgroup := hle
  have hv0 : ∀ h, (⟨b₁ 0, h⟩ : 𝒪.toAddSubgroup.toIntSubmodule) = x • b₂ 0 + y • b₂ 1 := by
    intro h
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul, hb₁0, hb₂0, hb₂1]
    exact hxy.symm
  have hv1 : ∀ h, (⟨b₁ 1, h⟩ : 𝒪.toAddSubgroup.toIntSubmodule) = z • b₂ 0 + w • b₂ 1 := by
    intro h
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul, hb₁1, hb₂0, hb₂1]
    exact hzw.symm
  have hfun : (fun i ↦ (⟨b₁ i, hle' (SetLike.coe_mem _)⟩ : 𝒪.toAddSubgroup.toIntSubmodule)) =
      ![x • b₂ 0 + y • b₂ 1, z • b₂ 0 + w • b₂ 1] := by
    funext i
    fin_cases i
    · exact hv0 _
    · exact hv1 _
  have hdet : (b₂.det fun i ↦ ⟨b₁ i, hle' (SetLike.coe_mem _)⟩) = x * w - z * y := by
    rw [hfun, Module.Basis.det_apply, Matrix.det_fin_two, Module.Basis.toMatrix_apply,
      Module.Basis.toMatrix_apply, Module.Basis.toMatrix_apply, Module.Basis.toMatrix_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, map_zsmul, b₂.repr_self, b₂.repr_self]
    simp
  -- `|α|² = a (xw - zy)`, from the imaginary parts of `ᾱ (α τ) = |α|² τ`
  have hxy' : (x : ℂ) + y * (a * τ) = α := by rw [← hxy, zsmul_eq_mul, zsmul_eq_mul, mul_one]
  have hzw' : (z : ℂ) + w * (a * τ) = α * τ := by rw [← hzw, zsmul_eq_mul, zsmul_eq_mul, mul_one]
  have e : conj ((x : ℂ) + y * (a * τ)) * (z + w * (a * τ)) = (normSq α : ℂ) * τ := by
    rw [hxy', hzw', ← mul_assoc, mul_comm (conj α), mul_conj]
  have him := congrArg Complex.im e
  simp only [map_add, map_mul, map_intCast, mul_im, add_im, add_re, mul_re,
    intCast_re, intCast_im, conj_re, conj_im, ofReal_re, ofReal_im] at him
  have hN : normSq α = a * ((x * w - z * y : ℤ) : ℝ) := by
    have h0 : (normSq α - a * ((x * w - z * y : ℤ) : ℝ)) * τ.im = 0 := by
      push_cast
      linear_combination -him
    exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right hτ0)
  have hpos : (0 : ℝ) < ((x * w - z * y : ℤ) : ℝ) := by
    have := normSq_pos.mpr hα
    rw [hN] at this
    exact pos_of_mul_pos_right this ha'.le
  rw [AddSubgroup.relIndex_eq_natAbs_det _ _ hle' b₁ b₂, hdet]
  refine ⟨?_, ?_⟩
  · rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos hpos, hN]
    field_simp
  · rw [Int.natAbs_ne_zero]
    exact_mod_cast hpos.ne'

end BinaryQuadraticForm

namespace PeriodPair

open BinaryQuadraticForm

/-- **A proper ideal times its conjugate.** Let $a, b, c \in \mathbb{Z}$ with $\gcd(a, b, c) = 1$,
$a > 0$ and $b^2 - 4ac < 0$, let $\tau \in \mathbb{C}$ satisfy $a\tau^2 + b\tau + c = 0$, let
$\alpha \in \mathbb{C}$ with $\alpha \neq 0$, and put $\mathcal{O} = \mathbb{Z} + \mathbb{Z}a\tau$.
Let $L$ be a period pair whose lattice is $L = \mathbb{Z}\alpha + \mathbb{Z}\alpha\tau$ and is
contained in $\mathcal{O}$, and let $N = [\mathcal{O} : L]$ be its index (as additive subgroups of
$\mathbb{C}$). Then, as $\mathbb{Z}$-submodules of $\mathbb{C}$, with $\bar{L}$ the image of $L$
under complex conjugation,
$$L\bar{L} = N\mathcal{O}, \qquad N \neq 0, \qquad L \cdot N^{-1}\bar{L} = \mathcal{O}.$$
When $L$ is a proper $\mathcal{O}$-ideal, Sutherland's proof puts it in exactly this form, and the
statement is $\mathfrak{a}\bar{\mathfrak{a}} = (N\mathfrak{a})$ with $N\mathfrak{a} = [\mathcal{O} :
\mathfrak{a}]$, so that $\mathfrak{a}^{-1} = \frac{1}{N\mathfrak{a}}\bar{\mathfrak{a}}$.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare, Fall
2025, Lecture 17, Theorem 17.10 and its proof, from the point where $\mathfrak{a} = \alpha[1, \tau]$
and $\mathcal{O} = [1, a\tau]$ have been obtained; the product formula
`BinaryQuadraticForm.span_mul_map_conj_span` and the index computation
`BinaryQuadraticForm.relIndex_span_pair_eq` are written out here. -/
theorem lattice_mul_map_conj_eq_relIndex_smul {a b c : ℤ}
    (hprim : Int.gcd (Int.gcd a b : ℤ) c = 1) (ha : 0 < a) (hD : discrim a b c < 0) {τ α : ℂ}
    (hτ : (a : ℂ) * τ ^ 2 + b * τ + c = 0) (hα : α ≠ 0) (L : PeriodPair)
    (hL : L.lattice = Submodule.span ℤ {α, α * τ})
    (hle : L.lattice ≤ Submodule.span ℤ {(1 : ℂ), a * τ}) :
    L.lattice * L.lattice.map (starRingEnd ℂ).toIntAlgHom.toLinearMap =
        ((L.lattice.toAddSubgroup.relIndex (Submodule.span ℤ {(1 : ℂ), a * τ}).toAddSubgroup :
          ℕ) : ℤ) • Submodule.span ℤ {(1 : ℂ), a * τ} ∧
      L.lattice.toAddSubgroup.relIndex (Submodule.span ℤ {(1 : ℂ), a * τ}).toAddSubgroup ≠ 0 ∧
      L.lattice * (((L.lattice.toAddSubgroup.relIndex
          (Submodule.span ℤ {(1 : ℂ), a * τ}).toAddSubgroup : ℕ) : ℂ)⁻¹ •
          L.lattice.map (starRingEnd ℂ).toIntAlgHom.toLinearMap) =
        Submodule.span ℤ {(1 : ℂ), a * τ} := by
  rw [hL] at hle ⊢
  obtain ⟨hidx, hne⟩ := relIndex_span_pair_eq ha hD hτ hα hle
  set N := (Submodule.span ℤ {α, α * τ}).toAddSubgroup.relIndex
    (Submodule.span ℤ {(1 : ℂ), a * τ}).toAddSubgroup
  have hNC : (N : ℂ) = ((normSq α / a : ℝ) : ℂ) := by
    rw [← hidx]
    push_cast
    rfl
  have hprod := span_mul_map_conj_span (α := α) hprim ha hD hτ
  refine ⟨?_, hne, ?_⟩
  · rw [int_smul_submodule_eq, Int.cast_natCast, hNC, hprod]
  · rw [map_conj_span_pair] at hprod ⊢
    rw [Submodule.smul_span, Submodule.span_mul_span, mul_smul_comm, ← Submodule.smul_span,
      ← Submodule.span_mul_span, hprod, smul_smul, ← hNC, inv_mul_cancel₀ (by exact_mod_cast hne),
      one_smul]

/-- **A proper ideal times its conjugate.** Let $\omega \in \mathbb{C}$ be non-real and let
$\mathcal{O} \subseteq \mathbb{C}$ be a subring whose underlying set is the lattice
$\mathbb{Z} + \mathbb{Z}\omega$, an order in an imaginary quadratic field. Let $\mathfrak{a}$ be the
lattice of a period pair $L$ that is a proper ideal of $\mathcal{O}$ (its endomorphism ring
$\{\lambda \in \mathbb{C} : \lambda\mathfrak{a} \subseteq \mathfrak{a}\}$ is $\mathcal{O}$) and is
contained in $\mathcal{O}$, and let $N = [\mathcal{O} : \mathfrak{a}]$ be its index. Then, with
$\bar{\mathfrak{a}}$ the complex conjugate lattice and products of $\mathbb{Z}$-submodules of
$\mathbb{C}$,
$$\mathfrak{a}\bar{\mathfrak{a}} = N\mathcal{O},$$
$N \neq 0$, and $\mathfrak{a} \cdot N^{-1}\bar{\mathfrak{a}} = \mathcal{O}$, so $\mathfrak{a}$ is
invertible with inverse $N^{-1}\bar{\mathfrak{a}}$.

No imaginary quadratic field is fixed in advance, and $\mathfrak{a}$ need not lie in one: properness
alone puts it, up to homothety, in $\mathbb{Q}(\omega)$.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare,
Fall 2025, Lecture 17, Theorem 17.10 and its proof
($\mathfrak{a}\bar{\mathfrak{a}} = (N\mathfrak{a})$ and
$\mathfrak{a}^{-1} = \frac{1}{N\mathfrak{a}}\bar{\mathfrak{a}}$ for a proper $\mathcal{O}$-ideal),
and Lecture 16, Definition 16.9 (proper ideals); the reduction to
`PeriodPair.lattice_mul_map_conj_eq_relIndex_smul` is written out here. -/
theorem lattice_mul_map_conj_eq_relIndex_smul_of_isProperIdeal {L : PeriodPair} {𝒪 : Subring ℂ}
    {ω : ℂ} (hω : ω.im ≠ 0) (h𝒪 : (𝒪 : Set ℂ) = (ofTau ω hω).lattice) (hL : L.IsProperIdeal 𝒪)
    (hle : (L.lattice : Set ℂ) ⊆ 𝒪) :
    L.lattice * L.lattice.map (starRingEnd ℂ).toIntAlgHom.toLinearMap =
        ((L.lattice.toAddSubgroup.relIndex (ofTau ω hω).lattice.toAddSubgroup : ℕ) : ℤ) •
          (ofTau ω hω).lattice ∧
      L.lattice.toAddSubgroup.relIndex (ofTau ω hω).lattice.toAddSubgroup ≠ 0 ∧
      L.lattice * (((L.lattice.toAddSubgroup.relIndex (ofTau ω hω).lattice.toAddSubgroup : ℕ) :
          ℂ)⁻¹ • L.lattice.map (starRingEnd ℂ).toIntAlgHom.toLinearMap) =
        (ofTau ω hω).lattice := by
  have hωO : ω ∈ 𝒪 := by
    rw [← SetLike.mem_coe, h𝒪]; exact mem_lattice_ofTau.mpr ⟨0, 1, by simp⟩
  have hmul : ω * ω ∈ (ofTau ω hω).lattice := by
    rw [← SetLike.mem_coe, ← h𝒪]; exact 𝒪.mul_mem hωO hωO
  obtain ⟨D, hD0, hD⟩ := exists_sq_sub_conj_eq_intCast hω hmul
  obtain ⟨a, b, c, τ, hprim, ha, hd, hroot, ⟨α, hα, hLset⟩, hset⟩ :=
    exists_root_of_isProperIdeal hω h𝒪 hD hL
  have hLspan : L.lattice = Submodule.span ℤ {α, α * (τ : ℂ)} := by
    ext z
    rw [← SetLike.mem_coe, hLset, Set.mem_smul_set, Submodule.mem_span_pair]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨m, n, rfl⟩ := mem_lattice_ofTau.mp hw
      exact ⟨m, n, by simp only [zsmul_eq_mul, smul_eq_mul]; ring⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨m + n * τ, mem_lattice_ofTau.mpr ⟨m, n, rfl⟩, by
        simp only [zsmul_eq_mul, smul_eq_mul]; ring⟩
  have hOspan : (ofTau ω hω).lattice = Submodule.span ℤ {(1 : ℂ), (a : ℂ) * τ} := by
    ext z
    rw [← SetLike.mem_coe, ← h𝒪, hset, Set.mem_ofPred_eq, Submodule.mem_span_pair]
    constructor
    · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by simp only [zsmul_eq_mul]; ring⟩
    · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by simp only [zsmul_eq_mul]; ring⟩
  have hle' : L.lattice ≤ Submodule.span ℤ {(1 : ℂ), (a : ℂ) * τ} := by
    rw [← hOspan]; intro z hz; rw [← SetLike.mem_coe, ← h𝒪]; exact hle hz
  rw [hOspan]
  exact lattice_mul_map_conj_eq_relIndex_smul hprim ha (hd ▸ hD0) hroot hα L hLspan hle'

end PeriodPair
