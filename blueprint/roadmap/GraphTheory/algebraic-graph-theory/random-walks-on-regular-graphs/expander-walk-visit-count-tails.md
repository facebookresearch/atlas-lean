# Selected-time hitting and visit-count tails for expander walks

Let $G$ be a regular multigraph on a finite nonempty set with spectral expansion $\eta$, let $W$ be a vertex set of density $\rho$, and put $q = \rho + \eta^2$. Take a uniformly started walk with $t$ independent uniform steps, $L = t + 1$ vertices, and let $X$ be the number of times $i \le t$ with $v_i \in W$. Then:

(1) for every set $S \subseteq \{0, \dots, t\}$ of times, $\Pr[\forall i \in S: v_i \in W] \le q^{|S|/2}$;

(2) $\mathbb{E}\binom{X}{m} \le \binom{L}{m} q^{m/2}$ for every $m$, and if $1 \le m \le L$ and $q > 0$, then $\Pr[X > m] < \binom{L}{m} q^{m/2}$;

(3) if $\eta < \sqrt{\rho}$, then $\Pr[X > \lfloor L/2 \rfloor] < (32\rho)^{L/4}$.

## Proof sketch

Part (1) is the varying-density product bound with $B_i = W$ for $i \in S$ and $B_i = V$ otherwise, using norm contraction instead of the factor $\sqrt{1 + \eta^2}$ at unrestricted times. Summing (1) over $m$-subsets gives the factorial-moment bound, and Markov's inequality on $\binom{X}{m}$ (with a gain at $X = m$) gives the strict tail. For (3) take $m = \lfloor L/2 \rfloor + 1$, use $q < 2\rho$ and $\binom{L}{m} \le 2^L$.

## Depends on

- [Spectral expansion, second eigenvalue and edge expansion of a regular multigraph](../../graph-families-and-operations/expander-graph-operations/spectral-expansion-second-eigenvalue-and-edge-expansion.md)

## Proof depends on

- [Expander walks with varying target densities: the product hitting bound](expander-walk-varying-density-hitting.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Chapters 7-8, public draft (March 2007), 2007.
- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science, 2012.
