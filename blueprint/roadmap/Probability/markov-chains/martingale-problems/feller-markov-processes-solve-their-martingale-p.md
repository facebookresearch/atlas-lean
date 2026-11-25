# Feller processes solve the martingale problem of their generator

Let $E$ be a compact metric space and $(T_t)_{t\ge0}$ a Feller semigroup on $C(E)$, that is, a strongly continuous semigroup of positive contractions with $T_t1=1$, with generator $A$ and domain $\mathcal D(A)$. Let $X$ be a process with càdlàg paths in $E$, adapted to a filtration $(\mathcal F_t)$, which is Markov with semigroup $(T_t)$ in the conditional-expectation form

$$\mathbb E\bigl[f(X_{t+s})\bigm|\mathcal F_t\bigr]=T_sf(X_t)\qquad\text{a.s., for all }f\in C(E),\ s,t\ge0 .$$

Then for every $f\in\mathcal D(A)$

$$f(X_t)-f(X_0)-\int_0^tAf(X_s)\,ds$$

is an $(\mathcal F_t)$-martingale, so $X$ solves the $(A,\mu)$ [martingale problem](martingale-problems-generic-definition.md) with $\mu$ the law of $X_0$. Continuous paths are a special case; the paths need not be continuous.

## Depends on

- [Martingale problems](martingale-problems-generic-definition.md)
- [Strongly continuous contraction semigroups, generators and cores](../../../Analysis/operator-theory/strongly-continuous-contraction-semigroups.md)

## Proof depends on

- [Integral identities for a strongly continuous semigroup and its generator](../../../Analysis/operator-theory/integral-identities-for-semigroup-generators.md)

## Expansion

A full proof page must establish:

- The semigroup identity $T_sf-f=\int_0^sT_uAf\,du$ in $C(E)$ for $f\in\mathcal D(A)$.
- For $t,s\ge0$: $\mathbb E[f(X_{t+s})-f(X_t)\mid\mathcal F_t]=T_sf(X_t)-f(X_t)=\int_0^sT_uAf(X_t)\,du=\mathbb E\bigl[\int_t^{t+s}Af(X_u)\,du\bigm|\mathcal F_t\bigr]$, the last step by Fubini and the Markov property, using joint measurability of $(u,\omega)\mapsto Af(X_u(\omega))$ from càdlàg paths.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://onlinelibrary.wiley.com/doi/book/10.1002/9780470316658>, Ch. 4 (Markov processes and martingale problems).
