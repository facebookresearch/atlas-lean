# Strong amplification requires a slowdown

For a family $\{G_N\}$ of population structures, let $\mathrm{FT}(G_N, r)$ be the expected number of generations ($N$ steps each) of the birth–death Moran process until absorption, started from one mutant of fitness $r > 1$ at a uniformly random vertex, and let the *timescale* $T(G_N)$ be its order of growth in $N$ (dropping lower-order terms and constants depending only on $r$). For the complete graph $T(K_N) = \log N$ (absorption takes about $(1 + 1/r)\log N$ generations), and for the Star $T(S_N) = N \log N$.

**Theorem 1 (Tkadlec–Pavlogiannis–Chatterjee–Nowak).** For every strong amplifier $\{G_N\}$ there is an increasing unbounded function $\beta(N)$ with

$$T(G_N) \ge \log N \cdot \beta(N).$$

Moreover one can take $\beta(N)$ of order $1/\mathrm{ep}(G_N, r)$, where $\mathrm{ep} = 1 - \mathrm{fp}$ is the extinction probability, which tends to $0$ for a strong amplifier. The same holds under temperature initialization.

Thus no strong amplifier fixes on the logarithmic timescale of a well-mixed population.

## Depends on

- [Amplifiers, strong amplifiers and initialization schemes](amplifiers-strong-amplifiers-and-initialization-schemes.md)

## Proof sketch

Let $p_{v \to u} = w_{vu}/\sum_x w_{vx}$ and the temperature $T(u) = \sum_{v \ne u} p_{v \to u}$. If $\mathrm{ep}(G_N, r) \to 0$, then a set $S$ of $\Theta(N)$ vertices must be **cold**, with $T(u) = O(\mathrm{ep}(G_N, r))$ for $u \in S$; otherwise a constant fraction of initial mutants would be replaced before reproducing. On the way to fixation the mutants must occupy all of $S$; filling the remaining cold vertices is a coupon-collector process needing $\Theta(N \log N)$ attempts, and each vertex of $S$ receives an attempt only once per $1/T(u)$ steps. Hence at least of order $N \log N / T(u)$ steps, that is $\log N \cdot \beta(N)$ generations with $\beta(N) \propto 1/\mathrm{ep}(G_N, r)$, are needed.

## Sources

- J. Tkadlec, A. Pavlogiannis, K. Chatterjee and M. A. Nowak, "Fast and strong amplifiers of natural selection", Nature Communications 12 (2021), article 4009, Results ("Two theorems", Theorem 1, Eq. (3)) and Methods ("The slowdown of strong amplifiers", Eqs. (5)–(6)); proofs in Supplementary Note 3, <https://doi.org/10.1038/s41467-021-24271-w>, PMCID PMC8242091.
