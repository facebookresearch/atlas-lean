# Absolute spectral gap and l2 contraction factor of a reversible chain

Let $P$ be a Markov kernel on a finite set $S$ with at least two states, reversible with respect to a distribution $\pi$ with $\pi(x) > 0$ for all $x$, and let $\langle f, g\rangle_\pi = \sum_x \pi(x) f(x) g(x)$ and $(Pf)(x) = \sum_y P(x,y) f(y)$. Over the nonzero functions $f$ with $\sum_x \pi(x) f(x) = 0$, define the *contraction factor*

$$
\lambda_\ast = \sup_f \frac{|\langle f, Pf\rangle_\pi|}{\langle f, f\rangle_\pi} = \sup_f \sqrt{\frac{\langle Pf, Pf\rangle_\pi}{\langle f, f\rangle_\pi}},
$$

the largest modulus of an eigenvalue of $P$ on the subspace of $\pi$-mean-zero functions, eigenvalues counted with multiplicity (the set of such $f$ is nonempty because $|S| \ge 2$); for irreducible $P$ these are exactly the eigenvalues other than the simple eigenvalue $1$, so $\lambda_\ast = \max\{|\lambda| : \lambda \text{ an eigenvalue of } P,\ \lambda \ne 1\}$, and the *absolute spectral gap* $\gamma_\ast = 1 - \lambda_\ast \in [0, 1]$. The relaxation time is $t_{\mathrm{rel}} = 1/\gamma_\ast$ when $\gamma_\ast > 0$ and $t_{\mathrm{rel}} = \infty$ when $\gamma_\ast = 0$. The (ordinary) spectral gap is $\gamma = 1 - \lambda_2$, the infimum of the Dirichlet form ratio. For the lazy chain $(I + P)/2$, which is reversible with respect to the same $\pi$, $\gamma_\ast = \gamma = \gamma(P)/2$.

## Depends on

- [Irreducible stochastic matrix](../../kolmogorov-s-criterion-for-reversibility/is-irreducible.md)
- [Spectral gap of a finite Markov kernel, in Dirichlet-form terms](../../dirichlet-forms/spectral-gap.md)
- [The Dirichlet form of a Markov kernel](../../dirichlet-forms/form-sub-one.md)
- [Reversible stochastic matrix](../../kolmogorov-s-criterion-for-reversibility/is-reversible.md)
- [The lazy version of a reversible stochastic matrix is reversible and stochastic](../../mixing-times-of-markov-chains/lazy-mem-row-stochastic-and-detailed-bal.md)

## Sources

- David A. Levin and Yuval Peres, "Markov Chains and Mixing Times", 2nd ed., American Mathematical Society, 2017.
