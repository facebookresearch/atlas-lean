# State-space form of the base-excited oscillator

**State-space form of the base-excited oscillator** (trajectory correspondence,
and the physical-to-canonical bridge). Let `m > 0`. The curve `s ↦ (u s, v s)` is a
trajectory of the plant `(baseExcitedA m c k, baseExcitedB m)` driven by the input
`s ↦ (pf s, ya s)` if and only if, at every time `t`, `u` has derivative `v t` and
`v` has a derivative `a` with `m * a + c * v t + k * u t = pf t - m * ya t`. Then
`v = u'` everywhere and `a = u''(t)`, so the right side says that `u` solves the
relative equation `m u'' + c u' + k u = p - m a_g`. For the owner record `S` that
`StateSpaceCoeffs.ofMatrix` builds from the four pinned matrices, the inline
trajectory condition on the owner record (the convention of
`MathlibExt.Analysis.Control.IsControllableOn`; the record itself carries no
trajectory semantics), `∀ t, HasDerivAt z (S.A (z t) + S.B (w t)) t` for
`z = (u, v)` and `w = (pf, ya)`, reduces to the left side by
`simp only [ofMatrix_A_apply, ofMatrix_B_apply]`. Physical domain `m > 0`, `c ≥ 0`,
`k > 0`; the equivalence holds for all real `c` and `k`.
