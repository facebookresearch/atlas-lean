# Path-level convergence of rescaled ancestral partition chains in Skorokhod space

Assume the Möhle–Sagitov conditions under which the ancestral partition chain of a sample of $n$ from a Cannings model, run at time scale $1/c_N$, has [transition matrices converging to Kingman's](tendsto-ancestral-matrix-pow.md). Then the rescaled chain converges in law, in the Skorokhod $J_1$ topology on $D([0, \infty), \mathcal{P}_n)$ with $\mathcal{P}_n$ the finite set of partitions of $[n]$, to Kingman's $n$-coalescent, the continuous-time Markov chain with the [finite-dimensional distributions](../../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-input-measure-real-ctmc-path-fdd.md) of its rate matrix.

The finite-dimensional part is [the matrix limit](tendsto-ancestral-matrix-pow.md). Tightness follows from the [criterion for finite state spaces](../../../../Probability/convergence-of-measures/skorokhod-space/sufficient-criterion-for-relative-compactness-an.md), part (b), with the bound: for every $T, \delta > 0$ and every $N$ with $c_N > 0$,

$$\mathbb{P}\bigl(\text{two mergers within } \delta \text{ of each other in } [0, T], \text{ or a merger in } (0, \delta], \text{ or a merger in } [T - \delta, T]\bigr) \le n \binom{n}{2} (\delta + c_N).$$

Proof of the bound:

1. From any state with $b \le n$ blocks the probability of some merger in one generation is at most $\binom{b}{2} c_N \le \binom{n}{2} c_N$, by a union bound over pairs, each of which shares a parent with probability exactly $c_N$.
2. A time window of length $\delta$ contains at most $\delta / c_N + 1$ generations, so by the Markov property at the start of the window, a merger in a window that starts at a stopping time has probability at most $\binom{n}{2} (\delta + c_N)$.
3. There are at most $n - 1$ mergers, so the event is contained in the union of the $n - 2$ windows started at the first $n - 2$ merger times and the two endpoint windows: $n$ windows in all.

## Depends on

- [Under Möhle–Sagitov, transition matrices converge to Kingman's](tendsto-ancestral-matrix-pow.md)
- [Finite-dimensional distributions](../../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-input-measure-real-ctmc-path-fdd.md)

## Proof depends on

- [J1 tightness criterion for finite-state pure-jump processes (jump separation)](../../../../Probability/convergence-of-measures/skorokhod-space/j1-tightness-criterion-for-finite-state-pure-jum.md)

## Expansion

1. The bound above, using the exact pair probability $c_N$ with no $o(1)$ term.
2. Tightness and convergence from the bound and the finite-dimensional limit. The limit has no fixed jump times.
3. A numerical check: for Kingman's coalescent with $n = 12$ and $\delta = 10^{-4}$, the exact short-gap probability is at least $0.02176$, below $n \binom{n}{2} \delta = 0.0792$.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658> (Skorokhod convergence of jump processes).
- M. Möhle and S. Sagitov, A classification of coalescent processes for haploid exchangeable population models, *Ann. Probab.* 29 (2001), 1547–1562, <https://doi.org/10.1214/aop/1015345761> (limit).
