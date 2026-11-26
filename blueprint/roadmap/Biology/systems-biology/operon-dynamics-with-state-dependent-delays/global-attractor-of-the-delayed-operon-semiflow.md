# Global existence, positivity and global attractor of the delayed operon model

Consider the [state-dependent-delay operon model](goodwin-operon-model-with-state-dependent-delays.md) with continuously differentiable velocities bounded between positive constants, $0<v_k^{\min}\le v_k\le v_k^{\max}$, and a continuously differentiable fraction $f$ with values between a positive minimum and $1$. Let $r\ge\max(a_M/v_M^{\min},a_I/v_I^{\min})$ bound the delays, and let the solutions define a semiflow $S_G$ on the solution manifold $X_G$ of continuously differentiable histories on $[-r,0]$ compatible with the equation. Then:

1. every solution exists for all $t\ge0$ and is bounded;
2. there is a box $Q=\prod_{k=1}^3\big[d_k^{-}/b_k,\ d_k^{+}/b_k\big]\subset(0,\infty)^3$, with constants determined by the parameter bounds, that attracts every solution and is positively invariant for histories with values in $Q$;
3. solutions with strictly positive initial histories stay strictly positive;
4. $S_G$ has a compact global attractor $A_G\subset X_G$, and every history in $A_G$ has all three components strictly positive on $[-r,0]$.

## Depends on

- [Goodwin operon model with state-dependent transcription and translation delays](goodwin-operon-model-with-state-dependent-delays.md)

## Expansion

The production term of each equation is bounded above and below by positive constants built from the velocity bounds, $e^{-\mu a/v^{\min}}$ and the bounds on $f$, so the variation-of-constants formula traps $M$, then $I$, then $E$ in successive intervals; this gives global existence, absorption into a neighbourhood of $Q$ and positivity. Point dissipativity, together with complete continuity of the semiflow for $t\ge r$ (derivatives are uniformly bounded after one delay interval, so Arzelà–Ascoli applies), yields a global attractor by Hale's theorem on dissipative semiflows.

## Sources

- T. Gedeon, A. R. Humphries, M. C. Mackey, H.-O. Walther, Z. Wang, "Operon dynamics with state dependent transcription and/or translation delays", J. Math. Biol. (2021), Appendix B, Propositions B1–B2, Corollary B3 and Theorem B4, <https://doi.org/10.1007/s00285-021-01693-0>.
