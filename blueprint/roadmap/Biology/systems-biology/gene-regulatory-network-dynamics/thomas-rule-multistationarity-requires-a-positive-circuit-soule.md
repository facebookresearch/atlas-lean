# Thomas' rule: multistationarity requires a positive circuit

Let $\Omega = \prod_{i=1}^n \Omega_i \subseteq \mathbb{R}^n$ be a product of intervals and $F : \Omega \to \mathbb{R}^n$ differentiable, with Jacobian $J(a)$. The interaction graph $G(a)$ has vertices $1, \dots, n$ and an edge $j \to i$ with the sign of $\partial F_i/\partial x_j(a)$ when this entry is nonzero; a circuit is positive if the product of its signs is positive, and a zero $a$ of $F$ is nondegenerate if $\det J(a) \ne 0$ (Soulé 2003, Sections 1.2 and 2). Soulé proves Thomas' conjecture (Theorem 1): if $\Omega$ is open and $F$ has at least two nondegenerate zeros in $\Omega$, then $G(a)$ contains a positive circuit for some $a \in \Omega$. The proof reduces to Theorem 1′, that if all principal minors of $-J(a)$ are nonnegative for every $a$ then $-F$ has at most one nondegenerate zero: the maps $-F + \lambda x$, $\lambda > 0$, have Jacobians with positive principal minors, hence are univalent by the theorem of Gale and Nikaidô, and a degree argument (Proposition 1) then excludes two nondegenerate zeros.

## Expansion

1. The model: differentiable maps on products of intervals, interaction graphs, circuit signs and nondegenerate zeros.
2. The expansion of principal minors of $-J(a)$ over hoopings of $G(-J(a))$ (Lemma 2 of the source), and the sign consequence when no circuit is positive.
3. The univalence theorem of Gale and Nikaidô for maps whose Jacobian has positive principal minors on a product of intervals.
4. Proposition 1 (the degree argument) and the conclusion; the application to genetic networks, where multistationarity is the mathematical form of differentiation.

## Sources

- C. Soulé, Graphic requirements for multistationarity, ComPlexUs 1 (2003), 123–133, Theorem 1, Theorem 1′ and Proposition 1. <https://arxiv.org/abs/q-bio/0403033>
- Original result: D. Gale and H. Nikaidô, The Jacobian matrix and global univalence of mappings, Math. Ann. 159 (1965), 81–93. <https://doi.org/10.1007/bf01360282> The univalence statement used follows Soulé, Section 3.2.
