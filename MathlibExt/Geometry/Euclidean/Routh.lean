/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

namespace MetaMathlibExt

private lemma Esymm_ofLp (w : Fin 2 → ℝ) (j : Fin 2) :
    ((EuclideanSpace.equiv (Fin 2) ℝ).symm w).ofLp j = w j := by simp

private lemma E_apply_ofLp (z : EuclideanSpace ℝ (Fin 2)) (j : Fin 2) :
    (EuclideanSpace.equiv (Fin 2) ℝ) z j = z.ofLp j := by simp

/-- **Routh's theorem.** Let $A, B, C$ be points of the Euclidean plane $\mathbb{R}^2$ whose
triangle (the convex hull of $\{A, B, C\}$) has nonzero area, and let $x, y, z$ be positive
reals with $xyz \ne 1$. Let $D = \frac{x}{x+1} B + \frac{1}{x+1} C$,
$E = \frac{1}{y+1} A + \frac{y}{y+1} C$ and $F = \frac{z}{z+1} A + \frac{1}{z+1} B$, the
points of the sides $BC$, $CA$, $AB$ with $DC/DB = x$, $EA/EC = y$ and $FB/FA = z$. If $P$
lies on the segments $BE$ and $CF$, $Q$ lies on the segments $CF$ and $AD$, and $R$ lies on
the segments $AD$ and $BE$, then the area of the triangle $PQR$ (the convex hull of
$\{P, Q, R\}$) is
$$\frac{(xyz - 1)^2}{(xy + y + 1)(yz + z + 1)(zx + x + 1)}$$
times the area of $ABC$. Areas are Lebesgue measures.

Proves `Wanted` entry `routh`.

Source: https://en.wikipedia.org/wiki/Routh%27s_theorem
-/
theorem routh :
    ∀ (A B C D E F P Q R : EuclideanSpace ℝ (Fin 2)) (x y z : ℝ),
      0 < x →
      0 < y →
      0 < z →
      x * y * z ≠ 1 →
      MeasureTheory.volume (convexHull ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2)))) ≠ 0 →
      D = (x / (x + 1)) • B + (1 / (x + 1)) • C →
      E = (1 / (y + 1)) • A + (y / (y + 1)) • C →
      F = (z / (z + 1)) • A + (1 / (z + 1)) • B →
      P ∈ convexHull ℝ ({B, E} : Set (EuclideanSpace ℝ (Fin 2))) →
      P ∈ convexHull ℝ ({C, F} : Set (EuclideanSpace ℝ (Fin 2))) →
      Q ∈ convexHull ℝ ({C, F} : Set (EuclideanSpace ℝ (Fin 2))) →
      Q ∈ convexHull ℝ ({A, D} : Set (EuclideanSpace ℝ (Fin 2))) →
      R ∈ convexHull ℝ ({A, D} : Set (EuclideanSpace ℝ (Fin 2))) →
      R ∈ convexHull ℝ ({B, E} : Set (EuclideanSpace ℝ (Fin 2))) →
      (MeasureTheory.volume (convexHull ℝ ({P, Q, R} : Set (EuclideanSpace ℝ (Fin 2))))).toReal =
        ((x * y * z - 1) ^ 2 / ((x * y + y + 1) * (y * z + z + 1) * (z * x + x + 1))) *
          (MeasureTheory.volume (convexHull ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))).toReal := by
  intro A B C D E F P Q R x y z hx hy hz hxyz hvol hD hE hF hPBE hPCF hQCF hQAD hRAD hRBE
  have hx1 : x + 1 ≠ 0 := by positivity
  have hy1 : y + 1 ≠ 0 := by positivity
  have hz1 : z + 1 ≠ 0 := by positivity
  have hS1 : y * z + z + 1 ≠ 0 := by positivity
  have hS2 : z * x + x + 1 ≠ 0 := by positivity
  have hS3 : x * y + y + 1 ≠ 0 := by positivity
  set u : EuclideanSpace ℝ (Fin 2) := B - A with hu
  set v : EuclideanSpace ℝ (Fin 2) := C - A with hv
  have aff : ∀ (c₁ c₂ : ℝ) (X Y : EuclideanSpace ℝ (Fin 2)), c₁ + c₂ = 1 →
      (c₁ • X + c₂ • Y - A) = c₁ • (X - A) + c₂ • (Y - A) := by
    intro c₁ c₂ X Y h
    have h0 : (c₁ + c₂ - 1) • A = (0 : EuclideanSpace ℝ (Fin 2)) := by simp [h]
    have hmod : c₁ • X + c₂ • Y - A
        = c₁ • (X - A) + c₂ • (Y - A) + (c₁ + c₂ - 1) • A := by module
    rw [hmod, h0, add_zero]
  have hsumD : x / (x + 1) + 1 / (x + 1) = 1 := by field_simp
  have hsumE : 1 / (y + 1) + y / (y + 1) = 1 := by field_simp <;> ring
  have hsumF : z / (z + 1) + 1 / (z + 1) = 1 := by field_simp
  have hDA : D - A = (x / (x + 1)) • u + (1 / (x + 1)) • v := by
    rw [hD, hu, hv]; exact aff _ _ _ _ hsumD
  have hEA : E - A = (y / (y + 1)) • v := by
    have h := aff (1 / (y + 1)) (y / (y + 1)) A C hsumE
    rw [sub_self, smul_zero, zero_add] at h
    rw [hE, hv]; exact h
  have hFA : F - A = (1 / (z + 1)) • u := by
    have h := aff (z / (z + 1)) (1 / (z + 1)) A B hsumF
    rw [sub_self, smul_zero, zero_add] at h
    rw [hF, hu]; exact h
  set El : (EuclideanSpace ℝ (Fin 2)) ≃ₗ[ℝ] (Fin 2 → ℝ) :=
    (EuclideanSpace.equiv (Fin 2) ℝ).toLinearEquiv with hEl
  have hElapp : ∀ (z : EuclideanSpace ℝ (Fin 2)) (j : Fin 2), El z j = z.ofLp j :=
    fun z j => E_apply_ofLp z j
  set b : Module.Basis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)) :=
    (Pi.basisFun ℝ (Fin 2)).map El.symm with hb
  have hrepr : ∀ (z : EuclideanSpace ℝ (Fin 2)) (i : Fin 2), b.repr z i = z.ofLp i := by
    intro z i
    rw [hb, Module.Basis.map_repr, LinearEquiv.symm_symm]
    simp only [LinearEquiv.trans_apply, Pi.basisFun_repr]
    exact E_apply_ofLp z i
  have hexpand : ∀ (w : EuclideanSpace ℝ (Fin 2)), w = (w.ofLp 0) • b 0 + (w.ofLp 1) • b 1 := by
    intro w
    have h := Module.Basis.sum_repr b w
    rw [Fin.sum_univ_two] at h
    simp only [hrepr] at h
    exact h.symm
  have hbi : ∀ i : Fin 2,
      b i = El.symm (Pi.single i 1) := by
    intro i; rw [hb, Module.Basis.map_apply, Pi.basisFun_apply]
  set Mf : Matrix (Fin 2) (Fin 2) ℝ :=
    !![u.ofLp 0, v.ofLp 0; u.ofLp 1, v.ofLp 1] with hMf
  set f : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) := b.constr ℝ (![u, v] : Fin 2 → EuclideanSpace ℝ (Fin 2)) with hf
  have hfu : f (b 0) = u := by rw [hf, Module.Basis.constr_basis]; simp
  have hfv : f (b 1) = v := by rw [hf, Module.Basis.constr_basis]; simp
  have hTM : LinearMap.toMatrix b b f = Mf := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, hfu, hfv, hrepr, hMf]
  have eM00 : Mf 0 0 = u.ofLp 0 := by rw [hMf]; simp
  have eM11 : Mf 1 1 = v.ofLp 1 := by rw [hMf]; simp
  have eM01 : Mf 0 1 = v.ofLp 0 := by rw [hMf]; simp
  have eM10 : Mf 1 0 = u.ofLp 1 := by rw [hMf]; simp
  have hdetM : Mf.det = u.ofLp 0 * v.ofLp 1 - u.ofLp 1 * v.ofLp 0 := by
    rw [Matrix.det_fin_two, eM00, eM11, eM01, eM10]
    ring
  have hdetf : f.det = Mf.det := by rw [← hTM, LinearMap.det_toMatrix]
  set T₀ : Set (EuclideanSpace ℝ (Fin 2)) := convexHull ℝ ({0, b 0, b 1} : Set (EuclideanSpace ℝ (Fin 2))) with hT₀
  have hT0 : f '' T₀ = convexHull ℝ ({0, u, v} : Set (EuclideanSpace ℝ (Fin 2))) := by
    rw [hT₀, LinearMap.image_convexHull]
    congr 1
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, map_zero, hfu, hfv]
  have htransHull : ∀ (O X Y Z : EuclideanSpace ℝ (Fin 2)),
      convexHull ℝ ({X, Y, Z} : Set (EuclideanSpace ℝ (Fin 2)))
        = (fun x => O +ᵥ x) '' convexHull ℝ ({X - O, Y - O, Z - O} : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro O X Y Z
    set φ : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
      { toFun := fun x => O +ᵥ x, linear := LinearMap.id,
        map_vadd' := fun p w => by
          simp only [vadd_eq_add, LinearMap.id_apply]
          exact add_left_comm O w p } with hφ
    have hfunphi : (fun x => O +ᵥ x) = ⇑φ := rfl
    have h1 : ({X, Y, Z} : Set (EuclideanSpace ℝ (Fin 2))) = ⇑φ '' ({X - O, Y - O, Z - O} : Set (EuclideanSpace ℝ (Fin 2))) := by
      have e1 : O +ᵥ (X - O) = X := by rw [vadd_eq_add]; exact add_sub_cancel O X
      have e2 : O +ᵥ (Y - O) = Y := by rw [vadd_eq_add]; exact add_sub_cancel O Y
      have e3 : O +ᵥ (Z - O) = Z := by rw [vadd_eq_add]; exact add_sub_cancel O Z
      have hφapp : ∀ w : EuclideanSpace ℝ (Fin 2), φ w = O +ᵥ w := fun w => rfl
      simp only [Set.image_insert_eq, Set.image_singleton, hφapp]
      rw [e1, e2, e3]
    rw [h1, hfunphi, ← AffineMap.image_convexHull]
  have htrans : ∀ (c : EuclideanSpace ℝ (Fin 2)) (S : Set (EuclideanSpace ℝ (Fin 2))), MeasureTheory.NullMeasurableSet S MeasureTheory.volume →
      MeasureTheory.volume ((fun x => c +ᵥ x) '' S) = MeasureTheory.volume S := by
    intro c S hS
    have hmp : MeasureTheory.MeasurePreserving (fun x => (-c) +ᵥ x) MeasureTheory.volume MeasureTheory.volume :=
      MeasureTheory.measurePreserving_vadd (-c) (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 2)))
    have hset : (fun x => (-c) +ᵥ x) ⁻¹' S = (fun x => c +ᵥ x) '' S := by
      ext x
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hx
        have he : c +ᵥ ((-c) +ᵥ x) = x := by simp only [vadd_eq_add]; abel
        exact ⟨(-c) +ᵥ x, hx, he⟩
      · rintro ⟨y, hy, rfl⟩
        have he : (-c) +ᵥ (c +ᵥ y) = y := by simp only [vadd_eq_add]; abel
        rw [he]; exact hy
    have hpre := hmp.measure_preimage (s := S) hS
    rw [hset] at hpre
    exact hpre
  have hnull : ∀ T : Set (EuclideanSpace ℝ (Fin 2)), IsCompact T → MeasureTheory.NullMeasurableSet T MeasureTheory.volume :=
    fun T hT => hT.isClosed.measurableSet.nullMeasurableSet
  have hfin3 : ∀ a b c : EuclideanSpace ℝ (Fin 2), ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2))).Finite := by
    intro a b c
    have hce : ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2))) = ↑({a, b, c} : Finset (EuclideanSpace ℝ (Fin 2))) := by simp
    rw [hce]; exact Finset.finite_toSet _
  have hABC : convexHull ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2)))
      = (fun x => A +ᵥ x) '' convexHull ℝ ({0, u, v} : Set (EuclideanSpace ℝ (Fin 2))) := by
    have h := htransHull A A B C
    rwa [sub_self, ← hu, ← hv] at h
  have hvolABC : MeasureTheory.volume (convexHull ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2))))
      = ENNReal.ofReal |f.det| * MeasureTheory.volume T₀ := by
    have hnull0 : MeasureTheory.NullMeasurableSet (f '' T₀) MeasureTheory.volume := by
      rw [hT0]
      exact hnull _ ((hfin3 0 u v).isCompact_convexHull ℝ)
    rw [hABC, ← hT0, htrans _ _ hnull0, MeasureTheory.Measure.addHaar_image_linearMap]
  have hdetne : f.det ≠ 0 := by
    intro h0
    apply hvol
    rw [hvolABC, h0, abs_zero, ENNReal.ofReal_zero, zero_mul]
  have key : ∀ (s t : ℝ), s • u + t • v = 0 → s = 0 ∧ t = 0 := by
    intro s t h
    have h1 : s * u.ofLp 0 + t * v.ofLp 0 = 0 := by
      have h1' := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => El w 0) h
      simp only [map_add, Pi.add_apply, map_smul, Pi.smul_apply, map_zero,
        Pi.zero_apply, smul_eq_mul, hElapp] at h1'
      exact h1'
    have h2 : s * u.ofLp 1 + t * v.ofLp 1 = 0 := by
      have h2' := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => El w 1) h
      simp only [map_add, Pi.add_apply, map_smul, Pi.smul_apply, map_zero,
        Pi.zero_apply, smul_eq_mul, hElapp] at h2'
      exact h2'
    have hdetMne : u.ofLp 0 * v.ofLp 1 - u.ofLp 1 * v.ofLp 0 ≠ 0 := by
      rw [← hdetM, ← hdetf]; exact hdetne
    have hs : s * (u.ofLp 0 * v.ofLp 1 - u.ofLp 1 * v.ofLp 0) = 0 := by
      linear_combination (v.ofLp 1) * h1 - (v.ofLp 0) * h2
    have ht : t * (u.ofLp 0 * v.ofLp 1 - u.ofLp 1 * v.ofLp 0) = 0 := by
      linear_combination (u.ofLp 0) * h2 - (u.ofLp 1) * h1
    exact ⟨(mul_eq_zero.mp hs).resolve_right hdetMne,
      (mul_eq_zero.mp ht).resolve_right hdetMne⟩
  have uniq' : ∀ (s₁ t₁ s₂ t₂ : ℝ),
      s₁ • u + t₁ • v = s₂ • u + t₂ • v → s₁ = s₂ ∧ t₁ = t₂ := by
    intro s₁ t₁ s₂ t₂ h
    have hexpand2 : (s₁ • u + t₁ • v) - (s₂ • u + t₂ • v)
        = (s₁ - s₂) • u + (t₁ - t₂) • v := by module
    have h0 : (s₁ - s₂) • u + (t₁ - t₂) • v = 0 := by
      rw [← hexpand2, h, sub_self]
    obtain ⟨hs, ht⟩ := key _ _ h0
    exact ⟨sub_eq_zero.mp hs, sub_eq_zero.mp ht⟩
  have hinjf : Function.Injective f := by
    intro a c hac
    have h0 : f (a - c) = 0 := by rw [map_sub, hac, sub_self]
    have hexp := hexpand (a - c)
    have h1 : ((a - c).ofLp 0) • u + ((a - c).ofLp 1) • v = 0 := by
      have h2 : f (((a - c).ofLp 0) • b 0 + ((a - c).ofLp 1) • b 1)
          = ((a - c).ofLp 0) • u + ((a - c).ofLp 1) • v := by
        rw [map_add, map_smul, map_smul, hfu, hfv]
      rw [← hexp] at h2
      rw [h0] at h2
      exact h2.symm
    obtain ⟨hs, ht⟩ := key _ _ h1
    have hac0 : a - c = 0 := by
      rw [hexp, hs, ht]
      simp
    exact sub_eq_zero.mp hac0
  have hsurj : Function.Surjective f := LinearMap.injective_iff_surjective.mp hinjf
  have hexist : ∀ (w : EuclideanSpace ℝ (Fin 2)), ∃ (s : ℝ) (t : ℝ),
      w = A + s • u + t • v := by
    intro w
    obtain ⟨z, hz⟩ := hsurj (w - A)
    have hexp := hexpand z
    have hfz : f z = (z.ofLp 0) • u + (z.ofLp 1) • v := by
      conv_lhs => rw [hexp]
      rw [map_add, map_smul, map_smul, hfu, hfv]
    refine ⟨z.ofLp 0, z.ofLp 1, ?_⟩
    have hw : w = A + f z := by rw [hz]; abel
    rw [hw, hfz, add_assoc]
  -- Coordinates of P
  obtain ⟨sP, tP, hsPtP⟩ := hexist P
  have hPsPtP : P - A = sP • u + tP • v := by rw [hsPtP]; abel
  have hPseg1 : P ∈ segment ℝ B E := by rw [← convexHull_pair]; exact hPBE
  rw [segment_eq_image] at hPseg1
  obtain ⟨lam, -, hlamP⟩ := hPseg1
  have hlamP' : (1 - lam) • B + lam • E = P := hlamP
  have hPeq1 : P - A = (1 - lam) • u + (lam * y / (y + 1)) • v := by
    have hbase := aff (1 - lam) lam B E (by ring)
    rw [hlamP'] at hbase
    rw [hbase, ← hu, hEA, ← mul_smul,
      show lam * (y / (y + 1)) = lam * y / (y + 1) from by ring]
  have hPseg2 : P ∈ segment ℝ C F := by rw [← convexHull_pair]; exact hPCF
  rw [segment_eq_image] at hPseg2
  obtain ⟨mu, -, hmuP⟩ := hPseg2
  have hmuP' : (1 - mu) • C + mu • F = P := hmuP
  have hPeq2 : P - A = (mu / (z + 1)) • u + (1 - mu) • v := by
    have hbase := aff (1 - mu) mu C F (by ring)
    rw [hmuP'] at hbase
    rw [hbase, ← hv, hFA, ← mul_smul,
      show mu * (1 / (z + 1)) = mu / (z + 1) from by ring]
    exact add_comm _ _
  have eP1 : sP = 1 - lam ∧ tP = lam * y / (y + 1) :=
    uniq' sP tP (1 - lam) (lam * y / (y + 1)) (by rw [← hPsPtP]; exact hPeq1)
  have eP2 : sP = mu / (z + 1) ∧ tP = 1 - mu :=
    uniq' sP tP (mu / (z + 1)) (1 - mu) (by rw [← hPsPtP]; exact hPeq2)
  have hlam : lam * (y * z + z + 1) = z * (y + 1) := by
    have g1 : sP * (z + 1) = mu := (eq_div_iff hz1).mp eP2.1
    have m1 : mu = (1 - lam) * (z + 1) := by rw [← g1, eP1.1]
    have t1 : tP = 1 - (1 - lam) * (z + 1) := by rw [eP2.2, m1]
    have g2 : lam * y = tP * (y + 1) := (div_eq_iff hy1).mp eP1.2.symm
    rw [t1] at g2
    linear_combination -g2
  have hlamv : lam = z * (y + 1) / (y * z + z + 1) := (eq_div_iff hS1).mpr hlam
  have hsP : sP = 1 / (y * z + z + 1) := by rw [eP1.1, hlamv]; field_simp <;> ring
  have htP : tP = y * z / (y * z + z + 1) := by rw [eP1.2, hlamv]; field_simp
  -- Coordinates of Q
  obtain ⟨sQ, tQ, hsQtQ⟩ := hexist Q
  have hQsQtQ : Q - A = sQ • u + tQ • v := by rw [hsQtQ]; abel
  have hQseg1 : Q ∈ segment ℝ C F := by rw [← convexHull_pair]; exact hQCF
  rw [segment_eq_image] at hQseg1
  obtain ⟨muQ, -, hmuQ⟩ := hQseg1
  have hmuQ' : (1 - muQ) • C + muQ • F = Q := hmuQ
  have hQeq1 : Q - A = (muQ / (z + 1)) • u + (1 - muQ) • v := by
    have hbase := aff (1 - muQ) muQ C F (by ring)
    rw [hmuQ'] at hbase
    rw [hbase, ← hv, hFA, ← mul_smul,
      show muQ * (1 / (z + 1)) = muQ / (z + 1) from by ring]
    exact add_comm _ _
  have hQseg2 : Q ∈ segment ℝ A D := by rw [← convexHull_pair]; exact hQAD
  rw [segment_eq_image] at hQseg2
  obtain ⟨nuQ, -, hnuQ⟩ := hQseg2
  have hnuQ' : (1 - nuQ) • A + nuQ • D = Q := hnuQ
  have hQeq2 : Q - A = (nuQ * x / (x + 1)) • u + (nuQ / (x + 1)) • v := by
    have hbase := aff (1 - nuQ) nuQ A D (by ring)
    rw [hnuQ'] at hbase
    rw [hbase, sub_self, smul_zero, zero_add, hDA, smul_add, ← mul_smul, ← mul_smul,
      show nuQ * (x / (x + 1)) = nuQ * x / (x + 1) from by ring,
      show nuQ * (1 / (x + 1)) = nuQ / (x + 1) from by ring]
  have eQ1 : sQ = muQ / (z + 1) ∧ tQ = 1 - muQ :=
    uniq' sQ tQ (muQ / (z + 1)) (1 - muQ) (by rw [← hQsQtQ]; exact hQeq1)
  have eQ2 : sQ = nuQ * x / (x + 1) ∧ tQ = nuQ / (x + 1) :=
    uniq' sQ tQ (nuQ * x / (x + 1)) (nuQ / (x + 1)) (by rw [← hQsQtQ]; exact hQeq2)
  have eQ1s : sQ * (z + 1) = muQ := (eq_div_iff hz1).mp eQ1.1
  have eQ2s : sQ * (x + 1) = nuQ * x := (eq_div_iff hx1).mp eQ2.1
  have eQ2t : tQ * (x + 1) = nuQ := (eq_div_iff hx1).mp eQ2.2
  have esQ : sQ = tQ * x := by
    have e5 : sQ * (x + 1) = (tQ * x) * (x + 1) := by rw [eQ2s, ← eQ2t]; ring
    exact mul_right_cancel₀ hx1 e5
  have htQ : tQ * (z * x + x + 1) = 1 := by
    linear_combination eQ1.2 + eQ1s - (z + 1) * esQ
  have htvQ : tQ = 1 / (z * x + x + 1) := (eq_div_iff hS2).mpr htQ
  have hsQ : sQ = x / (z * x + x + 1) := by rw [esQ, htvQ]; ring
  -- Coordinates of R
  obtain ⟨sR, tR, hsRtR⟩ := hexist R
  have hRsRtR : R - A = sR • u + tR • v := by rw [hsRtR]; abel
  have hRseg1 : R ∈ segment ℝ A D := by rw [← convexHull_pair]; exact hRAD
  rw [segment_eq_image] at hRseg1
  obtain ⟨nuR, -, hnuR⟩ := hRseg1
  have hnuR' : (1 - nuR) • A + nuR • D = R := hnuR
  have hReq1 : R - A = (nuR * x / (x + 1)) • u + (nuR / (x + 1)) • v := by
    have hbase := aff (1 - nuR) nuR A D (by ring)
    rw [hnuR'] at hbase
    rw [hbase, sub_self, smul_zero, zero_add, hDA, smul_add, ← mul_smul, ← mul_smul,
      show nuR * (x / (x + 1)) = nuR * x / (x + 1) from by ring,
      show nuR * (1 / (x + 1)) = nuR / (x + 1) from by ring]
  have hRseg2 : R ∈ segment ℝ B E := by rw [← convexHull_pair]; exact hRBE
  rw [segment_eq_image] at hRseg2
  obtain ⟨lamR, -, hlamR⟩ := hRseg2
  have hlamR' : (1 - lamR) • B + lamR • E = R := hlamR
  have hReq2 : R - A = (1 - lamR) • u + (lamR * y / (y + 1)) • v := by
    have hbase := aff (1 - lamR) lamR B E (by ring)
    rw [hlamR'] at hbase
    rw [hbase, ← hu, hEA, ← mul_smul,
      show lamR * (y / (y + 1)) = lamR * y / (y + 1) from by ring]
  have eR1 : sR = 1 - lamR ∧ tR = lamR * y / (y + 1) :=
    uniq' sR tR (1 - lamR) (lamR * y / (y + 1)) (by rw [← hRsRtR]; exact hReq2)
  have eR2 : sR = nuR * x / (x + 1) ∧ tR = nuR / (x + 1) :=
    uniq' sR tR (nuR * x / (x + 1)) (nuR / (x + 1)) (by rw [← hRsRtR]; exact hReq1)
  have eR2s : sR * (x + 1) = nuR * x := (eq_div_iff hx1).mp eR2.1
  have eR2t : tR * (x + 1) = nuR := (eq_div_iff hx1).mp eR2.2
  have esR : sR = tR * x := by
    have e5 : sR * (x + 1) = (tR * x) * (x + 1) := by rw [eR2s, ← eR2t]; ring
    exact mul_right_cancel₀ hx1 e5
  have gR : lamR * y = tR * (y + 1) := (div_eq_iff hy1).mp eR1.2.symm
  have mR : lamR = 1 - tR * x := by rw [← esR, eR1.1]; ring
  have keyR : tR * (x * y + y + 1) = y := by
    rw [mR] at gR
    linear_combination -gR
  have htvR : tR = y / (x * y + y + 1) := (eq_div_iff hS3).mpr keyR
  have hsR : sR = x * y / (x * y + y + 1) := by rw [esR, htvR]; ring
  -- Images under f
  set p' : EuclideanSpace ℝ (Fin 2) := (1 / (y * z + z + 1)) • b 0 + ((y * z) / (y * z + z + 1)) • b 1 with hp'
  set q' : EuclideanSpace ℝ (Fin 2) := (x / (z * x + x + 1)) • b 0 + (1 / (z * x + x + 1)) • b 1 with hq'
  set r' : EuclideanSpace ℝ (Fin 2) := ((x * y) / (x * y + y + 1)) • b 0 + (y / (x * y + y + 1)) • b 1 with hr'
  have hfp' : f p' = P - A := by
    rw [hp', map_add, map_smul, map_smul, hfu, hfv, ← hsP, ← htP, ← hPsPtP]
  have hfq' : f q' = Q - A := by
    rw [hq', map_add, map_smul, map_smul, hfu, hfv, ← hsQ, ← htvQ, ← hQsQtQ]
  have hfr' : f r' = R - A := by
    rw [hr', map_add, map_smul, map_smul, hfu, hfv, ← hsR, ← htvR, ← hRsRtR]
  set g : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) := b.constr ℝ (![q' - p', r' - p'] : Fin 2 → EuclideanSpace ℝ (Fin 2)) with hg
  have hgu : g (b 0) = q' - p' := by rw [hg, Module.Basis.constr_basis]; simp
  have hgv : g (b 1) = r' - p' := by rw [hg, Module.Basis.constr_basis]; simp
  have hcombo : ∀ (s t : ℝ),
      ((s • b 0 + t • b 1).ofLp 0 = s) ∧ ((s • b 0 + t • b 1).ofLp 1 = t) := by
    intro s t
    have e0 : El (b 0) = Pi.single (0 : Fin 2) (1 : ℝ) := by
      rw [hbi 0]; exact LinearEquiv.apply_symm_apply _ _
    have e1 : El (b 1) = Pi.single (1 : Fin 2) (1 : ℝ) := by
      rw [hbi 1]; exact LinearEquiv.apply_symm_apply _ _
    constructor
    · rw [← hElapp, map_add, map_smul, map_smul, e0, e1]
      simp [Pi.add_apply, Pi.smul_apply, Pi.single_apply]
    · rw [← hElapp, map_add, map_smul, map_smul, e0, e1]
      simp [Pi.add_apply, Pi.smul_apply, Pi.single_apply]
  set Mg : Matrix (Fin 2) (Fin 2) ℝ :=
    !![(q' - p').ofLp 0, (r' - p').ofLp 0;
       (q' - p').ofLp 1, (r' - p').ofLp 1] with hMg
  have hTMg : LinearMap.toMatrix b b g = Mg := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, hgu, hgv, hrepr, hMg]
  have m00 : Mg 0 0 = (q' - p').ofLp 0 := by rw [hMg]; simp
  have m10 : Mg 1 0 = (q' - p').ofLp 1 := by rw [hMg]; simp
  have m01 : Mg 0 1 = (r' - p').ofLp 0 := by rw [hMg]; simp
  have m11 : Mg 1 1 = (r' - p').ofLp 1 := by rw [hMg]; simp
  have hexpq : q' - p'
      = (x / (z * x + x + 1) - 1 / (y * z + z + 1)) • b 0
        + (1 / (z * x + x + 1) - (y * z) / (y * z + z + 1)) • b 1 := by
    rw [hq', hp']; module
  have hexpr : r' - p'
      = ((x * y) / (x * y + y + 1) - 1 / (y * z + z + 1)) • b 0
        + (y / (x * y + y + 1) - (y * z) / (y * z + z + 1)) • b 1 := by
    rw [hr', hp']; module
  have e00 : Mg 0 0 = x / (z * x + x + 1) - 1 / (y * z + z + 1) := by
    rw [m00, hexpq]; exact (hcombo _ _).1
  have e10 : Mg 1 0 = 1 / (z * x + x + 1) - (y * z) / (y * z + z + 1) := by
    rw [m10, hexpq]; exact (hcombo _ _).2
  have e01 : Mg 0 1 = (x * y) / (x * y + y + 1) - 1 / (y * z + z + 1) := by
    rw [m01, hexpr]; exact (hcombo _ _).1
  have e11 : Mg 1 1 = y / (x * y + y + 1) - (y * z) / (y * z + z + 1) := by
    rw [m11, hexpr]; exact (hcombo _ _).2
  have hdetg : g.det
      = (x * y * z - 1) ^ 2 / (((x * y + y + 1) * (y * z + z + 1)) * (z * x + x + 1)) := by
    rw [← LinearMap.det_toMatrix b g, hTMg, Matrix.det_fin_two, e00, e01, e10, e11]
    field_simp <;> ring
  set T₁ : Set (EuclideanSpace ℝ (Fin 2)) := convexHull ℝ ({p', q', r'} : Set (EuclideanSpace ℝ (Fin 2))) with hT₁
  have hgT0 : g '' T₀ = convexHull ℝ ({0, q' - p', r' - p'} : Set (EuclideanSpace ℝ (Fin 2))) := by
    rw [hT₀, LinearMap.image_convexHull]
    congr 1
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, map_zero, hgu, hgv]
  have hT1 : T₁ = (fun x => p' +ᵥ x) '' (g '' T₀) := by
    have h := htransHull p' p' q' r'
    rw [sub_self, ← hT₁, ← hgT0] at h
    exact h
  have hvolT1 : MeasureTheory.volume T₁ = ENNReal.ofReal |g.det| * MeasureTheory.volume T₀ := by
    have hnullg : MeasureTheory.NullMeasurableSet (g '' T₀) MeasureTheory.volume := by
      rw [hgT0]
      exact hnull _ ((hfin3 0 (q' - p') (r' - p')).isCompact_convexHull ℝ)
    rw [hT1, htrans _ _ hnullg, MeasureTheory.Measure.addHaar_image_linearMap]
  have hfT1 : f '' T₁ = convexHull ℝ ({P - A, Q - A, R - A} : Set (EuclideanSpace ℝ (Fin 2))) := by
    rw [hT₁, LinearMap.image_convexHull]
    congr 1
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, hfp', hfq', hfr']
  have hnullfT1 : MeasureTheory.NullMeasurableSet (f '' T₁) MeasureTheory.volume := by
    rw [hfT1]
    exact hnull _ ((hfin3 (P - A) (Q - A) (R - A)).isCompact_convexHull ℝ)
  have hPQR : convexHull ℝ ({P, Q, R} : Set (EuclideanSpace ℝ (Fin 2))) = (fun x => A +ᵥ x) '' (f '' T₁) := by
    rw [hfT1]; exact htransHull A P Q R
  have hvolPQR : MeasureTheory.volume (convexHull ℝ ({P, Q, R} : Set (EuclideanSpace ℝ (Fin 2))))
      = ENNReal.ofReal |g.det| * MeasureTheory.volume (convexHull ℝ ({A, B, C} : Set (EuclideanSpace ℝ (Fin 2)))) := by
    rw [hPQR, htrans _ _ hnullfT1, MeasureTheory.Measure.addHaar_image_linearMap,
      hvolT1, hvolABC]
    ring
  have hKnn : 0 ≤ (x * y * z - 1) ^ 2 / (((x * y + y + 1) * (y * z + z + 1)) * (z * x + x + 1)) := by
    positivity
  rw [hvolPQR, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), hdetg,
    abs_of_nonneg hKnn]

end MetaMathlibExt
