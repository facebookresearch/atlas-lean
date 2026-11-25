# Weyl comm of disjoint

Disjoint Weyl commutation over any `[Ring R]`: if `{i, j}` and `{k, l}`
are disjoint, witnessed by the four cross hypotheses `i ≠ k`, `i ≠ l`,
`j ≠ k`, `j ≠ l` (together with `i ≠ j` and `k ≠ l`), then `weyl i j u`
commutes with `weyl k l v` for all units `u v`. The proof unfolds `weyl` and
derives the four distinct `x`-factor `Commute` facts from `x_comm` via
`commutatorElement_eq_one_iff_commute.mp`, then composes them with
`Commute.mul_left`/`Commute.mul_right` to cover the repeated `3 × 3` factors.
This is the isolated disjoint-word prerequisite for the even-length boundary
descent. It claims no torus/cocycle identity, no finite containment, no
termination/TWT, no kernel generation, and no Matsumoto theorem.
