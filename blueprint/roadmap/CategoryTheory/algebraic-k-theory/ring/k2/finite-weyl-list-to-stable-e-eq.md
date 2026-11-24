# Stable Steinberg Finite Weyl List Eval

List-level `StableE` image of a finite Weyl word: `toStableE` of the
head-left `List.ofFn`/`List.prod` ordered product of
`weyl (a k) (b k) (hab k) (u k)` over `k : Fin m` is the ordered product of the
three-factor finite `StableE.elementary` realizations at `⟨a k, ha k⟩`,
`⟨b k, hb k⟩` with coefficients `u k`, `-(u k)⁻¹`, `u k`, in the same head-left
order and orientation as `finiteWeyl_toStableE_eq_finiteElementary`. Hypotheses
are the pointwise bounds `ha hb` and distinctness `hab`; the empty list gives
`1 = 1`. Purpose: finite word realization input. Nonclaims: no monomial product
uniqueness, torus landing, central-kernel containment, TWT, kernel-generation,
or Matsumoto claim.
