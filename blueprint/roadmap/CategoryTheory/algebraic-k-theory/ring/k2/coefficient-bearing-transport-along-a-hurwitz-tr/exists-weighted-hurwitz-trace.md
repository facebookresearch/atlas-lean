# Exists weighted hurwitz trace

Coefficients transport forward along a Hurwitz trace, product preserved.

Purpose: lift a pure forward `HurwitzReach w w'` trace to paired words: every
coefficient-carrying word over `w` reaches one over `w'` with the identical
`weightedWeylProd`. Orientation is head-left and forward: each single step
rewrites `Wₐ(u) * W_b(v)` to `W_b(v) * W_{conjLabel b a}(q)` with the exact
witness `q` from `exists_weylOfSwapLabel_mul_eq_rightHurwitz`, and the trace
recursion follows the pinned `Relation.ReflTransGen` order. Hypotheses:
`[Ring R]` only. Nonclaims: no symmetric/left/reverse closure, no
terminal-pair deletion, no torus/cocycle landing, no strict
descent/termination, no finite `List.ofFn` bridge, no kernel generation, no
TWT, and no Matsumoto theorem.
