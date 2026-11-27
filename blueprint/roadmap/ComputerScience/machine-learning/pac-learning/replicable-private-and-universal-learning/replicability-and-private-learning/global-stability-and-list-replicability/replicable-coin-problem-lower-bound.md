# Replicability costs a quadratic factor in the replicability parameter

A randomized algorithm $A(S; r)$ taking an i.i.d. sample $S$ from a distribution $D$ and internal randomness $r$ is **$\rho$-replicable** if $\Pr_{S, S' \sim D^n,\, r}[A(S; r) = A(S'; r)] \ge 1 - \rho$ for every $D$, where $S, S', r$ are independent and the same $r$ is used in both runs. In the **$\tau$-coin problem** one observes i.i.d. bits of bias $p \in [0,1]$ and must output $1$ if $p \ge \tfrac12 + \tau$ and $0$ if $p \le \tfrac12 - \tau$ (either output allowed otherwise). For $\tau > 0$ and $\delta < 1/16$ (the proof takes $\tau < 1/4$ and $\rho < 1/16$), every $\rho$-replicable algorithm solving the $\tau$-coin problem with success probability at least $1 - \delta$ needs $\Omega(\tau^{-2} \rho^{-2})$ samples, whereas $O(\tau^{-2}\log(1/\delta))$ samples suffice without replicability. Hence the rounding-based simulation of statistical queries is optimal in its dependence on $\rho$.

## Proof sketch

Fix the shared randomness $r$ and consider $f_r(p) = \Pr_S[A(S; r) = 1]$ as $p$ moves from $\tfrac12 - \tau$ to $\tfrac12 + \tau$: it moves from at most $\delta$ to at least $1 - \delta$ and is a polynomial of degree $n$ with derivative bounded by $O(\sqrt{n})$ in the relevant range. Hence for a random bias in the middle range, $f_r(p)$ lies in $[1/3, 2/3]$ with probability $\Omega(1/(\tau\sqrt{n}))$ over $p$ and $r$, and there two independent runs disagree with constant probability; averaging over $p$ gives non-replicability $\Omega(1/(\tau\sqrt{n}))$, so $\rho$-replicability forces $n = \Omega(1/(\tau^2\rho^2))$.

## Depends on

- [Replicable algorithms with shared randomness](../../../replicable-learning/replicable-algorithms-with-shared-seed.md)

## Proof depends on

- [Replicable simulation of a statistical query by randomized rounding](replicable-statistical-query-simulation.md)

## Sources

- R. Impagliazzo, R. Lei, T. Pitassi, J. Sorrell, "Reproducibility in Learning", STOC (2022), arXiv:2201.08430, Theorems 1.6 and 7.1 and Lemma 7.2.
