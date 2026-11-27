# Identification of limits of measure-valued processes as Fleming–Viot solutions

Let $E$ be a compact metric space and $B$ a bounded jump-type mutation operator on $C(E)$, and let $\mu^N$ be $\mathcal M_1(E)$-valued Markov processes with generators $A_N$. Suppose that

- $\sup_\mu |A_N \Phi_f(\mu) - A \Phi_f(\mu)| \to 0$ for every polynomial test function $\Phi_f$, as for the [Moran approximation of the Fleming–Viot generator](finite-type-moran-approximation-of-the-fleming-v.md), where $A$ is the Fleming–Viot generator;
- the laws of the $\mu^N$ are [C-tight](tightness-of-measure-valued-approximations-in-c.md) on $D([0, T], \mathcal M_1(E))$;
- the initial laws converge weakly to $\mu_0$.

Then every subsequential limit in law of $(\mu^N)$ has continuous paths and solves the Fleming–Viot martingale problem for $(A, \mu_0)$ on polynomial test functions. The graph of $A$ on polynomials has a countable core: the rational linear span of the pairs $(\Phi_f, A\Phi_f)$ with $f$ in a countable dense subset of each $C(E^n)$ is dense in the bounded-pointwise sense, since $\Phi_{f_k} \to \Phi_f$ and $A \Phi_{f_k} \to A \Phi_f$ uniformly when $f_k \to f$ uniformly. For finite $E$ this is the identification of limits of $K$-allele processes as the $K$-allele Wright–Fisher diffusion.

## Depends on

- [Finite-type / Moran approximation of the Fleming-Viot generator](finite-type-moran-approximation-of-the-fleming-v.md)
- [Tightness of measure-valued approximations in C([0,T], M1(E))](tightness-of-measure-valued-approximations-in-c.md)

## Proof depends on

- [Existence by approximation: limits of chains solve the limit martingale problem](../../../../Probability/markov-chains/martingale-problems/existence-by-approximation-limits-of-chains-solv.md)
- [Countable bounded-pointwise graph core for martingale problems](../../../../Probability/markov-chains/martingale-problems/countable-bounded-pointwise-graph-core-for-marti.md)

## Expansion

A full proof page must still establish:

- the passage to the limit in the martingale identities along the countable core;
- the finite-type case.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, Chapter 4 (identification of limits), <https://onlinelibrary.wiley.com/doi/book/10.1002/9780470316658>
