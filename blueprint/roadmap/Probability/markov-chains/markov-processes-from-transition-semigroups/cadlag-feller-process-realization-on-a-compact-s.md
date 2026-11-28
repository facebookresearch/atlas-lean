# Cadlag Feller process realization on a compact state space

Let $E$ be a compact metric space and $(T_t)_{t\ge0}$ a Feller semigroup on $C(E)$: positive linear contractions with $T_t1=1$, $T_0=I$, $T_{s+t}=T_sT_t$, and $\|T_tf-f\|_\infty\to0$ as $t\to0$ for every $f\in C(E)$. By the [representation of positive operators by Markov kernels](exists-markov-kernel-of-positive-operato.md), $T_tf(x)=\int f(y)\,K_t(x,dy)$ for Markov kernels $K_t$ satisfying the Chapman–Kolmogorov equations with $K_0(x,\cdot)=\delta_x$. Then for every $x\in E$ there is a probability measure $P_x$ on $D([0,\infty),E)$, with $x\mapsto P_x(\Gamma)$ measurable for every Borel set $\Gamma$, under which the coordinate process $X$ starts at $x$, is a Markov process with transition kernels $(K_t)$, and satisfies

$$T_tf(x)=\mathbb E_x\,f(X_t)\qquad(f\in C(E),\ t\ge0).$$

Its finite-dimensional laws are those of the [path-space measure of the semigroup](path-measure.md). Moreover $X$ is strong Markov with respect to the right-continuous augmentation of its natural filtration.

## Depends on

- [Positive operators on $C(E)$ are given by Markov kernels](exists-markov-kernel-of-positive-operato.md)
- [Path-space measure of a Markov semigroup](path-measure.md)
- [Skorokhod space D([0,T],E) for a metric space E: J1 topology and embeddings](../../convergence-of-measures/skorokhod-space/skorokhod-space-d-0-t-e-for-a-metric-space-e-j1.md)

## Proof depends on

- [Optional stopping for right-continuous martingales](../../martingales/stopping-times-and-martingale-problems/optional-stopping-right-continuous.md)

## Expansion

A proof page must establish: the kernels $K_t$ and their Chapman–Kolmogorov equations from the semigroup property; a càdlàg modification of the canonical process under the path measure, for instance from supermartingale regularization of $t\mapsto e^{-\lambda t}R_\lambda f(X_t)$ for the resolvent $R_\lambda=\int_0^\infty e^{-\lambda t}T_t\,dt$ and a countable separating family of $f$; the transfer of the law to $D([0,\infty),E)$ and measurability in $x$; and the strong Markov property, first for stopping times with countably many values and then by right-continuity and the Feller property.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://onlinelibrary.wiley.com/doi/book/10.1002/9780470316658>, Chapter 4 (càdlàg realization of Feller semigroups).
