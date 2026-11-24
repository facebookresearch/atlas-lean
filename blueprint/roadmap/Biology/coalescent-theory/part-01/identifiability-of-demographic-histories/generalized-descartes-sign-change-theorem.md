# A generalized Descartes rule of signs for demographic identifiability

Bhaskar and Song (2014, Theorem 4) prove a generalized Descartes rule of signs: if $f : \mathbb{R}_{\ge 0} \to \mathbb{R}$ is piecewise continuous, not identically zero, with a finite number $\sigma(f)$ of sign changes, then $G(x) = \int_0^\infty f(t)e^{-tx}\,dt$ has at most $\sigma(f)$ real roots, counted with multiplicity. From it they derive identifiability of population-size histories from the first-coalescence means $(c_2, \dots, c_n)$: for a function family $F$ of finite sign-change complexity $S(F)$, two distinct models in $F$ give distinct $(c_2, \dots, c_n)$ when $n \ge S(F) + 2$ (Theorem 5), and models with $K$ pieces from $F$ when $n \ge 2K + (2K - 1)S(F)$ (Theorem 6); in particular piecewise-constant histories with $K$ pieces are identified when $n \ge 2K$, a tight bound (Corollary 7), piecewise-exponential ones when $n \ge 4K - 1$ (Corollary 8), and piecewise generalized-exponential ones when $n \ge 6K - 2$ (Corollary 9). The target is these statements with the source's definitions of sign-change complexity and of the piecewise model classes.

## Expansion

1. Theorem 4 for a piecewise-continuous function with finitely many sign changes, with the integrability needed for $G$ to be defined.
2. The first-coalescence means as values of a Laplace transform: $c_m = \int_0^\infty\tilde\eta(\tau)e^{-\binom m2\tau}\,d\tau$ for the time-rescaled history $\tilde\eta$ (their eq. (4)).
3. Sign-change complexity of a function family, and its value for the constant, exponential and generalized-exponential families.
4. The identifiability theorem: two distinct histories with $K$ pieces have distinct $(c_2, \dots, c_n)$ for $n$ above the explicit bound.
5. Identifiability of piecewise-constant histories (the [Bhaskar–Song identifiability](../../site-frequency-spectrum-under-variable-populatio/size-fn-eq-of-first-coal-mean-eq.md)) as the special case.

## Sources

- A. Bhaskar and Y. S. Song, Descartes' rule of signs and the identifiability of population demographic models from genomic variation data, Ann. Statist. 42 (2014), 2469–2493. <https://arxiv.org/abs/1309.5056>
