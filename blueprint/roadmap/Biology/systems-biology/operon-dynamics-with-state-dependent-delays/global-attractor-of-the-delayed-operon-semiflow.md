# Global existence, positivity and global attractor of the delayed operon model

Consider the [state-dependent-delay operon model](goodwin-operon-model-with-state-dependent-delays.md) with positive gain coefficients $\beta_M,\beta_I,\beta_E>0$, positive loss rates $\bar\gamma_M,\bar\gamma_I,\bar\gamma_E>0$, continuously differentiable velocities bounded between positive constants, $0<v_k^{\min}\le v_k\le v_k^{\max}$, and a continuously differentiable fraction $f$ with values between a positive minimum and $1$. Let the history length $r$ strictly exceed every possible delay, $r>\max(a_M/v_M^{\min},a_I/v_I^{\min})$, and let the solutions define a semiflow $S_G$ on the set $X_G$ of continuously differentiable histories on $[-r,0]$ compatible with the equation, with the $C^1$ norm. Then:

1. every solution exists for all $t\ge0$ and is bounded;
2. there is a box $Q=\prod_{k=1}^3\big[d_k^{-}/b_k,\ d_k^{+}/b_k\big]\subset(0,\infty)^3$, with constants determined by the parameter bounds, that attracts every solution and is positively invariant for histories with values in $Q$;
3. solutions with strictly positive initial histories stay strictly positive;
4. $S_G$ has a global attractor $A_G\subset X_G$, compact in the $C^1$ norm, and every history in $A_G$ has all three components strictly positive on $[-r,0]$.

## Depends on

- [Goodwin operon model with state-dependent transcription and translation delays](goodwin-operon-model-with-state-dependent-delays.md)

## Proof depends on

- [Goodwin operon model with state-dependent transcription and translation delays](goodwin-operon-model-with-state-dependent-delays.md)
- [Duhamel's formula (variation of constants)](../../../Analysis/ordinary-differential-equations/duhamel-variation-of-constants.md)

## Expansion

The strict inequality $r>a_k/v_k^{\min}$ lets each delay be defined as the unique root in $(0,r)$ of its threshold condition, continuously differentiable in the history (Proposition A1). The components are then bounded successively: the production term of the $M$ equation is bounded above and below by positive constants built from $\beta_M$, the velocity bounds, $e^{-\mu a_M/v_M^{\min}}$ and the bounds on $f$, so the variation-of-constants formula with rate $\bar\gamma_M$ traps $M$; the bound on $M$ then bounds the production term of $I$, and the bound on $I$ that of $E$. This gives global existence, absorption into every neighbourhood of $Q$, positive invariance of histories with values in $Q$, and positivity, hence point dissipativity. For a bounded set of histories, the solutions and their derivatives are uniformly bounded, so the segments at time $r$ are bounded and equicontinuous in $C$; the derivatives are $G$ applied to the segments, and uniform continuity of the right-hand side on the compact closure of those segments makes the derivatives equicontinuous as well. Arzelà–Ascoli applied to the segments and to their derivatives gives precompactness in the $C^1$ norm, so the semiflow is completely continuous for $t\ge r$, and Hale's theorem on point-dissipative, completely continuous semiflows yields the global attractor.

## Sources

- T. Gedeon, A. R. Humphries, M. C. Mackey, H.-O. Walther, Z. Wang, "Operon dynamics with state dependent transcription and/or translation delays", J. Math. Biol. 84 (2022), article 2, Appendix A (Proposition A1) and Appendix B (Propositions B1–B2, Corollary B3 and Theorem B4), <https://doi.org/10.1007/s00285-021-01693-0>.
