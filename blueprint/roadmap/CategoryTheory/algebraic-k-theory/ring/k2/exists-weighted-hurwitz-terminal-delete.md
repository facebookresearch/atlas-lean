# Stable Steinberg Finite Weyl Hurwitz Delete

Terminal equal-denotation weighted Weyl deletion.

Purpose: delete an adjacent equal-denotation terminal pair from a
coefficient-carrying Weyl word, keeping head-left orientation throughout
(matching `weightedWeylProd`). Hypotheses: `[Field F]` only, a paired word
`wc` projecting to `pre ++ [t₁, t₂] ++ suf`, and equal swap denotations
`swapDenote t₁ = swapDenote t₂`. The coefficients `u v` are read
existentially from the actual word by a sound split. Equal denotations give
exactly two cases: ordered-equal labels use
`StableSteinberg.weyl_samePair_mul_eq_cocycle_mul_torus` with residual
`r = (-u) * v⁻¹`, while reversed-endpoint labels first rewrite the second
Weyl factor into `t₁` orientation by `StableSteinberg.weyl_swap` and then use
the same-pair theorem with residual `r = (-u) * (-(v⁻¹))⁻¹`. The cocycle
defect `c` moves past the prefix product to the far left by centrality; the
torus residual stays at the deletion site and lands in
`finiteTorusSubgroup n`. The shortened word projects to `pre ++ suf` with
the exact two-letter length drop.

Nonclaims: no vanishing defect (`c = 1` is false in general) or vanishing
torus, no torus transport through the suffix or ordered normal form, no
termination or global induction, no kernel generation, no TWT, and no
Matsumoto result.
