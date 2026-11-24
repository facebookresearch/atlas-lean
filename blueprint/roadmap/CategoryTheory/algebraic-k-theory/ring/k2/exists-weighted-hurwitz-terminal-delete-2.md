# Stable Steinberg Finite Weyl Hurwitz Delete Transport

Terminal equal-denotation weighted deletion with the residual transported
through the suffix.

Purpose: delete an adjacent equal-denotation terminal pair from a
coefficient-carrying Weyl word and move the resulting at-site torus residual
right past the suffix word, keeping head-left orientation throughout
(matching `weightedWeylProd`). Hypotheses: `[Field F]` only, a paired word
`wc` projecting to `pre ++ [t₁, t₂] ++ suf`, and equal swap denotations
`swapDenote t₁ = swapDenote t₂`. The shortened word is `wcPre ++ wcSuf`,
reused from the deletion packet together with its `pre ++ suf` projection
and the exact two-letter length drop. The transported label `a'` and
coefficient `r'` are existential, and the transported torus stays in
`finiteTorusSubgroup n`. Defects combine in canonical temporal order
`c_d * c_t`: the deletion defect first, the transport defect second, with
only the central `c_t` commuted left across the prefix product.

Nonclaims: no `wordProd`/permutation-kernel hypothesis or conclusion, no
global Hurwitz reach, no well-founded induction or termination, no arbitrary
finite-torus normal form, no kernel generation, no TWT, and no Matsumoto
theorem.
