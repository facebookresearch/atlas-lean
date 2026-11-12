/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicTensorTentMorera








open Filter Set Topology

namespace StatMech.Universality

noncomputable section



theorem eventually_norm_sub_lt_on_compact_of_tendstoLocallyUniformlyOn
    {ι : Type*} {p : Filter ι} {F : ι -> Complex -> Complex}
    {f : Complex -> Complex} (h : TendstoLocallyUniformlyOn F f p Set.univ)
    (K : Set Complex) (hK : IsCompact K) (epsilon : Real)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ n in p, forall z, z ∈ K -> norm (F n z - f z) < epsilon := by
  have hu : TendstoUniformlyOn F f p K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
      (h.mono (Set.subset_univ K))
  rw [Metric.uniformity_basis_dist.tendstoUniformlyOn_iff_of_uniformity] at hu
  simpa only [Prod.fst, Prod.snd, Set.mem_setOf_eq, dist_eq_norm, norm_sub_rev] using
    hu epsilon hepsilon



theorem isConservativeOn_univ_of_ordered_wedgeContour_eq_zero
    (f : Complex -> Complex)
    (hordered : forall z w : Complex, z.re <= w.re -> z.im <= w.im ->
      Complex.wedgeIntegral z w f + Complex.wedgeIntegral w z f = 0) :
    Complex.IsConservativeOn f Set.univ := by
  intro z w _hrect
  rw [← add_eq_zero_iff_eq_neg]
  by_cases hre : z.re <= w.re
  · by_cases him : z.im <= w.im
    · exact hordered z w hre him
    · have him' : w.im <= z.im := le_of_not_ge him
      let southwest : Complex := (z.re : Complex) + w.im * Complex.I
      let northeast : Complex := (w.re : Complex) + z.im * Complex.I
      have h := hordered southwest northeast (by simp [southwest, northeast, hre])
        (by simp [southwest, northeast, him'])
      rw [Complex.wedgeIntegral_add_wedgeIntegral_eq] at h ⊢
      simp only [southwest, northeast, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add,
        add_zero, sub_zero] at h
      rw [intervalIntegral.integral_symm w.im z.im,
        intervalIntegral.integral_symm w.im z.im]
      linear_combination -h
  · have hre' : w.re <= z.re := le_of_not_ge hre
    by_cases him : z.im <= w.im
    · let southwest : Complex := (w.re : Complex) + z.im * Complex.I
      let northeast : Complex := (z.re : Complex) + w.im * Complex.I
      have h := hordered southwest northeast (by simp [southwest, northeast, hre'])
        (by simp [southwest, northeast, him])
      rw [Complex.wedgeIntegral_add_wedgeIntegral_eq] at h ⊢
      simp only [southwest, northeast, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add,
        add_zero, sub_zero] at h
      rw [intervalIntegral.integral_symm w.re z.re,
        intervalIntegral.integral_symm w.re z.re]
      linear_combination -h
    · have him' : w.im <= z.im := le_of_not_ge him
      simpa [add_comm] using hordered w z hre' him'



def axisTwoEdgeStaircaseBaseSet
    (x y mesh : Real) (width height : Nat) : Set Complex :=
  {a | Or
    (exists k, k < width /\
      a = (x + (k : Real) * mesh : Real) + y * Complex.I)
    (Or
      (exists k, k < height /\
        a = (x + (width : Real) * mesh : Real) +
          (y + (k : Real) * mesh : Real) * Complex.I)
      (Or
        (exists k, k < width /\
          a = (x + (width : Real) * mesh - (k : Real) * mesh : Real) +
            (y + (height : Real) * mesh : Real) * Complex.I)
        (exists k, k < height /\
          a = x + (y + (height : Real) * mesh - (k : Real) * mesh : Real) *
            Complex.I)))}



theorem
    norm_axisTwoEdgeStaircasePathIntegral_sub_axisMacroDirectContour_le_of_baseOscillation
    (f : Complex -> Complex) (hf : Continuous f)
    (x y mesh epsilon : Real) (width height : Nat)
    (hmesh : 0 < mesh) (hepsilon : 0 <= epsilon)
    (hosc : forall a, a ∈ axisTwoEdgeStaircaseBaseSet
        x y mesh width height -> forall q : Complex,
      norm (q - a) <= 2 * mesh ->
      norm (f q - f a) <= epsilon) :
    norm (axisTwoEdgeStaircasePathIntegral f x y mesh width height -
      axisMacroDirectContour f x y mesh width height) <=
        8 * epsilon * mesh * ((width + height : Nat) : Real) := by
  let u : Complex := (mesh : Complex) / 2 * (1 - Complex.I)
  let v : Complex := (mesh : Complex) / 2 * (1 + Complex.I)
  have hu : norm u <= mesh := by
    calc
      norm u = norm ((mesh : Complex) / 2) * norm (1 - Complex.I) := by
        simp only [u, norm_mul]
      _ <= norm ((mesh : Complex) / 2) * 2 := by
        gcongr
        have h := norm_sub_le (1 : Complex) Complex.I
        norm_num at h ⊢
        exact h
      _ = mesh := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmesh]
        norm_num
  have hv : norm v <= mesh := by
    calc
      norm v = norm ((mesh : Complex) / 2) * norm (1 + Complex.I) := by
        simp only [v, norm_mul]
      _ <= norm ((mesh : Complex) / 2) * 2 := by
        gcongr
        have h := norm_add_le (1 : Complex) Complex.I
        norm_num at h ⊢
        exact h
      _ = mesh := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmesh]
        norm_num
  have hside (N : Nat) (a : Nat -> Complex) (p q : Complex)
      (hp : norm p <= mesh) (hq : norm q <= mesh)
      (ha : forall k, k < N ->
        a k ∈ axisTwoEdgeStaircaseBaseSet x y mesh width height) :
      norm ((∑ k ∈ Finset.range N,
          (complexDisplacementIntegral f (a k) p +
            complexDisplacementIntegral f (a k + p) q)) -
        ∑ k ∈ Finset.range N,
          complexDisplacementIntegral f (a k) (p + q)) <=
        4 * epsilon * mesh * (N : Real) := by
    have hlocal := norm_sum_twoEdgePath_sub_direct_le_of_ball
      f hf N a p q epsilon mesh hp hq
      (fun k hk z hz => hosc (a k) (ha k hk) z hz)
    calc
      norm ((∑ k ∈ Finset.range N,
          (complexDisplacementIntegral f (a k) p +
            complexDisplacementIntegral f (a k + p) q)) -
        ∑ k ∈ Finset.range N,
          complexDisplacementIntegral f (a k) (p + q)) <=
          ∑ k ∈ Finset.range N,
            epsilon * (norm p + norm q + norm (p + q)) := hlocal
      _ <= ∑ _k ∈ Finset.range N, epsilon * (4 * mesh) := by
        apply Finset.sum_le_sum
        intro k hk
        have hpq : norm (p + q) <= 2 * mesh :=
          (norm_add_le p q).trans (by linarith)
        exact mul_le_mul_of_nonneg_left (by linarith) hepsilon
      _ = 4 * epsilon * mesh * (N : Real) := by
        simp
        ring
  let bottom : Complex :=
    (∑ k ∈ Finset.range width,
        (complexDisplacementIntegral f
            (((x + (k : Real) * mesh : Real) : Complex) +
              (y : Complex) * Complex.I) u +
          complexDisplacementIntegral f
            ((((x + (k : Real) * mesh : Real) : Complex) +
              (y : Complex) * Complex.I) + u) v)) -
      ∑ k ∈ Finset.range width,
        complexDisplacementIntegral f
          (((x + (k : Real) * mesh : Real) : Complex) +
            (y : Complex) * Complex.I) (u + v)
  let right : Complex :=
    (∑ k ∈ Finset.range height,
        (complexDisplacementIntegral f
            (((x + (width : Real) * mesh : Real) : Complex) +
              (y + (k : Real) * mesh : Real) * Complex.I) v +
          complexDisplacementIntegral f
            ((((x + (width : Real) * mesh : Real) : Complex) +
              (y + (k : Real) * mesh : Real) * Complex.I) + v) (-u))) -
      ∑ k ∈ Finset.range height,
        complexDisplacementIntegral f
          (((x + (width : Real) * mesh : Real) : Complex) +
            (y + (k : Real) * mesh : Real) * Complex.I) (v + -u)
  let top : Complex :=
    (∑ k ∈ Finset.range width,
        (complexDisplacementIntegral f
            (((x + (width : Real) * mesh - (k : Real) * mesh : Real) :
                Complex) +
              (y + (height : Real) * mesh : Real) * Complex.I) (-u) +
          complexDisplacementIntegral f
            ((((x + (width : Real) * mesh - (k : Real) * mesh : Real) :
                Complex) +
              (y + (height : Real) * mesh : Real) * Complex.I) - u) (-v))) -
      ∑ k ∈ Finset.range width,
        complexDisplacementIntegral f
          (((x + (width : Real) * mesh - (k : Real) * mesh : Real) :
              Complex) +
            (y + (height : Real) * mesh : Real) * Complex.I) (-u + -v)
  let left : Complex :=
    (∑ k ∈ Finset.range height,
        (complexDisplacementIntegral f
            ((x : Complex) +
              (y + (height : Real) * mesh - (k : Real) * mesh : Real) *
                Complex.I) (-v) +
          complexDisplacementIntegral f
            (((x : Complex) +
              (y + (height : Real) * mesh - (k : Real) * mesh : Real) *
                Complex.I) - v) u)) -
      ∑ k ∈ Finset.range height,
        complexDisplacementIntegral f
          ((x : Complex) +
            (y + (height : Real) * mesh - (k : Real) * mesh : Real) *
              Complex.I) (-v + u)
  have hbottom : norm bottom <= 4 * epsilon * mesh * (width : Real) := by
    exact hside width
      (fun k => ((x + (k : Real) * mesh : Real) : Complex) +
        (y : Complex) * Complex.I) u v hu hv (by
          intro k hk
          exact Or.inl ⟨k, hk, rfl⟩)
  have hright : norm right <= 4 * epsilon * mesh * (height : Real) := by
    exact hside height
      (fun k => ((x + (width : Real) * mesh : Real) : Complex) +
        (y + (k : Real) * mesh : Real) * Complex.I) v (-u) hv (by simpa) (by
          intro k hk
          exact Or.inr (Or.inl ⟨k, hk, rfl⟩))
  have htop : norm top <= 4 * epsilon * mesh * (width : Real) := by
    exact hside width
      (fun k =>
        ((x + (width : Real) * mesh - (k : Real) * mesh : Real) :
            Complex) +
          (y + (height : Real) * mesh : Real) * Complex.I)
      (-u) (-v) (by simpa) (by simpa) (by
        intro k hk
        exact Or.inr (Or.inr (Or.inl ⟨k, hk, rfl⟩)))
  have hleft : norm left <= 4 * epsilon * mesh * (height : Real) := by
    exact hside height
      (fun k => (x : Complex) +
        (y + (height : Real) * mesh - (k : Real) * mesh : Real) * Complex.I)
      (-v) u (by simpa) hu (by
        intro k hk
        exact Or.inr (Or.inr (Or.inr ⟨k, hk, rfl⟩)))
  have huv : u + v = (mesh : Complex) := by
    dsimp only [u, v]
    ring
  have hvnu : v + -u = (mesh : Complex) * Complex.I := by
    dsimp only [u, v]
    ring
  have hnuv : -u + -v = (-mesh : Real) := by
    rw [← neg_add, huv]
    norm_num
  have hnvu : -v + u = ((-mesh : Real) : Complex) * Complex.I := by
    dsimp only [u, v]
    push_cast
    ring
  have htopDirect :
      (∑ k ∈ Finset.range width,
        complexDisplacementIntegral f
          ((x + (width : Real) * mesh + (k : Real) * (-mesh) : Real) +
            (y + (height : Real) * mesh : Real) * Complex.I)
          ((-mesh : Real) : Complex)) =
      ∑ k ∈ Finset.range width,
        complexDisplacementIntegral f
          ((x + (width : Real) * mesh - (k : Real) * mesh : Real) +
            (y + (height : Real) * mesh : Real) * Complex.I)
          ((-mesh : Real) : Complex) := by
    apply Finset.sum_congr rfl
    intro k hk
    congr 2
    push_cast
    ring
  have hleftDirect :
      (∑ k ∈ Finset.range height,
        complexDisplacementIntegral f
          (x + (y + (height : Real) * mesh +
            (k : Real) * (-mesh) : Real) * Complex.I)
          (((-mesh : Real) : Complex) * Complex.I)) =
      ∑ k ∈ Finset.range height,
        complexDisplacementIntegral f
          (x + (y + (height : Real) * mesh -
            (k : Real) * mesh : Real) * Complex.I)
          (((-mesh : Real) : Complex) * Complex.I) := by
    apply Finset.sum_congr rfl
    intro k hk
    congr 2
    push_cast
    ring
  have hdecompose :
      axisTwoEdgeStaircasePathIntegral f x y mesh width height -
          axisMacroDirectContour f x y mesh width height =
        bottom + right + top + left := by
    unfold axisTwoEdgeStaircasePathIntegral axisMacroDirectContour
    dsimp only
    simp only [show (mesh : Complex) / 2 * (1 - Complex.I) = u by rfl,
      show (mesh : Complex) / 2 * (1 + Complex.I) = v by rfl]
    rw [htopDirect, hleftDirect]
    rw [← hvnu, ← hnvu, ← hnuv, ← huv]
    dsimp only [bottom, right, top, left]
    ring
  rw [hdecompose]
  calc
    norm (bottom + right + top + left) <=
        norm bottom + norm right + norm top + norm left := by
      calc
        norm (bottom + right + top + left) <=
            norm (bottom + right + top) + norm left := norm_add_le _ _
        _ <= (norm (bottom + right) + norm top) + norm left := by
          gcongr
          exact norm_add_le _ _
        _ <= norm bottom + norm right + norm top + norm left := by
          gcongr
          exact norm_add_le _ _
    _ <= 8 * epsilon * mesh * ((width + height : Nat) : Real) := by
      push_cast
      linarith



theorem norm_axisTwoEdgeStaircasePathIntegral_sub_le_of_baseError
    (F G : Complex -> Complex) (hF : Continuous F) (hG : Continuous G)
    (x y mesh : Real) (width height : Nat) (epsilon : Real)
    (hmesh : 0 < mesh) (hepsilon : 0 <= epsilon)
    (herror : forall a, a ∈ axisTwoEdgeStaircaseBaseSet
        x y mesh width height -> forall q : Complex,
      norm (q - a) <= 2 * mesh -> norm (F q - G q) <= epsilon) :
    norm (axisTwoEdgeStaircasePathIntegral F x y mesh width height -
      axisTwoEdgeStaircasePathIntegral G x y mesh width height) <=
        4 * epsilon * mesh * ((width + height : Nat) : Real) := by
  let u : Complex := (mesh : Complex) / 2 * (1 - Complex.I)
  let v : Complex := (mesh : Complex) / 2 * (1 + Complex.I)
  let ab : Nat -> Complex := fun k =>
    (x + (k : Real) * mesh : Real) + y * Complex.I
  let ar : Nat -> Complex := fun k =>
    (x + (width : Real) * mesh : Real) +
      (y + (k : Real) * mesh : Real) * Complex.I
  let atop : Nat -> Complex := fun k =>
    (x + (width : Real) * mesh - (k : Real) * mesh : Real) +
      (y + (height : Real) * mesh : Real) * Complex.I
  let al : Nat -> Complex := fun k =>
    x + (y + (height : Real) * mesh - (k : Real) * mesh : Real) * Complex.I
  have hu : norm u <= mesh := by
    calc
      norm u = norm ((mesh : Complex) / 2) * norm (1 - Complex.I) := by
        simp only [u, norm_mul]
      _ <= norm ((mesh : Complex) / 2) * 2 := by
        gcongr
        have h := norm_sub_le (1 : Complex) Complex.I
        norm_num at h ⊢
        exact h
      _ = mesh := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmesh]
        norm_num
  have hv : norm v <= mesh := by
    calc
      norm v = norm ((mesh : Complex) / 2) * norm (1 + Complex.I) := by
        simp only [v, norm_mul]
      _ <= norm ((mesh : Complex) / 2) * 2 := by
        gcongr
        have h := norm_add_le (1 : Complex) Complex.I
        norm_num at h ⊢
        exact h
      _ = mesh := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmesh]
        norm_num
  have hpathDistance (a du dv q : Complex)
      (hdu : norm du <= mesh) (hdv : norm dv <= mesh)
      (hq : Or
        (exists t, t ∈ Set.Icc (0 : Real) 1 /\
          q = a + (t : Complex) * du)
        (exists t, t ∈ Set.Icc (0 : Real) 1 /\
          q = a + du + (t : Complex) * dv)) :
      norm (q - a) <= 2 * mesh := by
    rcases hq with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
    · rw [show a + (t : Complex) * du - a = (t : Complex) * du by ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have htNorm : |t| <= 1 := by
        rw [abs_le]
        constructor <;> linarith [ht.1, ht.2]
      calc
        |t| * norm du <= 1 * mesh :=
          mul_le_mul htNorm hdu (norm_nonneg du) (by norm_num)
        _ <= 2 * mesh := by linarith
    · rw [show a + du + (t : Complex) * dv - a =
        du + (t : Complex) * dv by ring]
      calc
        norm (du + (t : Complex) * dv) <=
            norm du + norm ((t : Complex) * dv) := norm_add_le _ _
        _ = norm du + |t| * norm dv := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ <= 2 * mesh := by
          have htNorm : |t| <= 1 := by
            rw [abs_le]
            constructor <;> linarith [ht.1, ht.2]
          have hmul : |t| * norm dv <= mesh := by
            simpa using mul_le_mul htNorm hdv (norm_nonneg dv) (by norm_num)
          linarith
  have sideBound (N : Nat) (a : Nat -> Complex) (du dv : Complex)
      (hdu : norm du <= mesh) (hdv : norm dv <= mesh)
      (ha : forall k, k < N ->
        a k ∈ axisTwoEdgeStaircaseBaseSet x y mesh width height) :
      norm ((∑ k ∈ Finset.range N,
          (complexDisplacementIntegral F (a k) du +
            complexDisplacementIntegral F (a k + du) dv)) -
        ∑ k ∈ Finset.range N,
          (complexDisplacementIntegral G (a k) du +
            complexDisplacementIntegral G (a k + du) dv)) <=
        2 * epsilon * mesh * (N : Real) := by
    calc
      _ <= ∑ k ∈ Finset.range N,
          epsilon * (norm du + norm dv) :=
        norm_sum_twoEdgePath_sub_le_of_uniformNorm
          F G hF hG N a du dv epsilon (by
            intro k hk q hq
            exact herror (a k) (ha k hk) q
              (hpathDistance (a k) du dv q hdu hdv hq))
      _ <= ∑ _k ∈ Finset.range N, 2 * epsilon * mesh := by
        apply Finset.sum_le_sum
        intro k hk
        nlinarith
      _ = 2 * epsilon * mesh * (N : Real) := by
        simp
        ring
  have hb := sideBound width ab u v hu hv (by
    intro k hk
    exact Or.inl ⟨k, hk, rfl⟩)
  have hr := sideBound height ar v (-u) hv (by simpa using hu) (by
    intro k hk
    exact Or.inr (Or.inl ⟨k, hk, rfl⟩))
  have ht := sideBound width atop (-u) (-v)
    (by simpa using hu) (by simpa using hv) (by
      intro k hk
      exact Or.inr (Or.inr (Or.inl ⟨k, hk, rfl⟩)))
  have hl := sideBound height al (-v) u (by simpa using hv) hu (by
    intro k hk
    exact Or.inr (Or.inr (Or.inr ⟨k, hk, rfl⟩)))
  have ht' :
      norm ((∑ k ∈ Finset.range width,
          (complexDisplacementIntegral F (atop k) (-u) +
            complexDisplacementIntegral F (atop k - u) (-v))) -
        ∑ k ∈ Finset.range width,
          (complexDisplacementIntegral G (atop k) (-u) +
            complexDisplacementIntegral G (atop k - u) (-v))) <=
        2 * epsilon * mesh * (width : Real) := by
    simpa [sub_eq_add_neg] using ht
  have hl' :
      norm ((∑ k ∈ Finset.range height,
          (complexDisplacementIntegral F (al k) (-v) +
            complexDisplacementIntegral F (al k - v) u)) -
        ∑ k ∈ Finset.range height,
          (complexDisplacementIntegral G (al k) (-v) +
            complexDisplacementIntegral G (al k - v) u)) <=
        2 * epsilon * mesh * (height : Real) := by
    simpa [sub_eq_add_neg] using hl
  have hdecompose :
      axisTwoEdgeStaircasePathIntegral F x y mesh width height -
          axisTwoEdgeStaircasePathIntegral G x y mesh width height =
        ((∑ k ∈ Finset.range width,
            (complexDisplacementIntegral F (ab k) u +
              complexDisplacementIntegral F (ab k + u) v)) -
          ∑ k ∈ Finset.range width,
            (complexDisplacementIntegral G (ab k) u +
              complexDisplacementIntegral G (ab k + u) v)) +
        ((∑ k ∈ Finset.range height,
            (complexDisplacementIntegral F (ar k) v +
              complexDisplacementIntegral F (ar k + v) (-u))) -
          ∑ k ∈ Finset.range height,
            (complexDisplacementIntegral G (ar k) v +
              complexDisplacementIntegral G (ar k + v) (-u))) +
        ((∑ k ∈ Finset.range width,
            (complexDisplacementIntegral F (atop k) (-u) +
              complexDisplacementIntegral F (atop k - u) (-v))) -
          ∑ k ∈ Finset.range width,
            (complexDisplacementIntegral G (atop k) (-u) +
              complexDisplacementIntegral G (atop k - u) (-v))) +
        ((∑ k ∈ Finset.range height,
            (complexDisplacementIntegral F (al k) (-v) +
              complexDisplacementIntegral F (al k - v) u)) -
          ∑ k ∈ Finset.range height,
            (complexDisplacementIntegral G (al k) (-v) +
              complexDisplacementIntegral G (al k - v) u)) := by
    unfold axisTwoEdgeStaircasePathIntegral
    dsimp only [u, v, ab, ar, atop, al]
    ring
  rw [hdecompose]
  calc
    norm (_ + _ + _ + _) <= norm (_ + _ + _) + norm _ := norm_add_le _ _
    _ <= (norm (_ + _) + norm _) + norm _ := by
      gcongr
      exact norm_add_le _ _
    _ <= ((norm _ + norm _) + norm _) + norm _ := by
      gcongr
      exact norm_add_le _ _
    _ <= (2 * epsilon * mesh * (width : Real) +
          2 * epsilon * mesh * (height : Real)) +
        2 * epsilon * mesh * (width : Real) +
          2 * epsilon * mesh * (height : Real) := by
      exact add_le_add (add_le_add (add_le_add hb hr) ht') hl'
    _ = 4 * epsilon * mesh * ((width + height : Nat) : Real) := by
      push_cast
      ring



theorem norm_axisTwoEdgeStaircasePathIntegral_sub_axisMacroDirectContour_le
    (f : Complex -> Complex) (hf : Continuous f)
    (x y mesh epsilon : Real) (width height : Nat)
    (hmesh : 0 < mesh)
    (hosc : forall a q : Complex, norm (q - a) <= 2 * mesh ->
      norm (f q - f a) <= epsilon) :
    norm (axisTwoEdgeStaircasePathIntegral f x y mesh width height -
      axisMacroDirectContour f x y mesh width height) <=
        8 * epsilon * mesh * ((width + height : Nat) : Real) := by
  have hepsilon : 0 <= epsilon := by
    have h := hosc 0 0 (by simpa using hmesh.le)
    simpa using h
  exact
    norm_axisTwoEdgeStaircasePathIntegral_sub_axisMacroDirectContour_le_of_baseOscillation
      f hf x y mesh epsilon width height hmesh hepsilon
      (fun a _ha q hq => hosc a q hq)

end

end StatMech.Universality
