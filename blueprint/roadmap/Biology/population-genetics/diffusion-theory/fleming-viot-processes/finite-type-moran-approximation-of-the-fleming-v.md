# Moran approximation of the Fleming–Viot generator

Let $E$ be a compact metric space and $B$ a bounded jump-type mutation generator on $C(E)$, so that $\mathcal D(B) = C(E)$, and let $A$ be the Fleming–Viot generator on polynomial test functions $\Phi_f(\mu) = \langle f, \mu^{\otimes n} \rangle$, $f \in C(E^n)$. Let $A_N$ be the generator of the empirical measure of the [Moran particle system with mutation](moran-particle-system-with-feller-mutation-on-a.md) of $N$ particles, acting on functions of $\mu \in \mathcal M_1^N(E)$, the probability measures on $E$ whose masses are multiples of $1/N$. Then for every $n \ge 1$ and $f \in C(E^n)$,

$$\sup_{\mu \in \mathcal M_1^N(E)} \bigl|A_N \Phi_f(\mu) - A \Phi_f(\mu)\bigr| \longrightarrow 0 \qquad (N \to \infty).$$

Since $B$ is bounded, no restriction of $f$ to a core of $B$ is needed. For a finite type space with $K$ types this is the convergence of the $K$-allele Moran generator to the $K$-allele Wright–Fisher generator on polynomials. The statement is a generator calculation only; it does not by itself give convergence of the processes.

## Depends on

- [Moran particle system with Feller mutation on a compact type space](moran-particle-system-with-feller-mutation-on-a.md)

## Proof depends on

- [Finite-type Fleming–Viot and Wright–Fisher martingale problems](finite-type-fleming-viot-k-allele-wright-fisher.md)

## Expansion

A full proof page must still establish:

- the computation of $A_N \Phi_f$ for the Moran system, with its sampling-without-replacement corrections of order $1/N$, uniformly in $\mu$;
- the finite-type case.

## Sources

- D. A. Dawson, "Measure-valued Markov processes", in *École d'Été de Probabilités de Saint-Flour XXI–1991*, Lecture Notes in Mathematics 1541, Springer, 1993, Moran approximation of Fleming–Viot, <https://link.springer.com/chapter/10.1007/BFb0084190>
- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, Chapter 10, <https://onlinelibrary.wiley.com/doi/book/10.1002/9780470316658>
