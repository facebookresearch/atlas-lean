# Selection reactors are fast strong amplifiers

**Selection reactor.** For integers $N > n \ge 1$ and probabilities $p_{\mathrm{in}}, p_{\mathrm{out}} \in (0,1)$, the selection reactor $\mathrm{SR}_N(n, p_{\mathrm{in}}, p_{\mathrm{out}})$ is the weighted graph on $N$ vertices with a well-mixed **hub** of $n$ vertices (all hub pairs joined with weight $w_h$), $\ell = N - n$ **leaves** each carrying a self-loop of weight $w_\ell$, and weight-$1$ edges between every hub vertex and every leaf. Its weights are chosen so that a reproducing leaf places its offspring in the hub with probability $p_{\mathrm{in}} = n/(n + w_\ell)$ and a reproducing hub vertex places its offspring on a leaf with probability $p_{\mathrm{out}} = (N - n)/((N - n) + (n - 1) w_h)$. Individuals compete directly only inside the hub.

Given an unbounded slowly growing function $\alpha$ with $1 < \alpha(N) \ll \sqrt N$, let $\mathrm{SR}^\alpha_N$ have $n = \lfloor N/\alpha(N) \rfloor$ and $p_{\mathrm{in}} = p_{\mathrm{out}} = 1/\alpha(N)^2$.

**Theorem 2 (Tkadlec–Pavlogiannis–Chatterjee–Nowak).** For every fixed $r > 1$, $\mathrm{fp}(\mathrm{SR}^\alpha_N, r) \to 1$ and

$$T(\mathrm{SR}^\alpha_N) \le \log N \cdot \alpha(N)^5 .$$

Consequently, for every increasing unbounded $\beta(N)$ there is a strong amplifier with $T(G_N) \le \log N \cdot \beta(N)$ (take $\alpha = \beta^{1/5}$); e.g. $\beta(N) = \log\log N$ gives timescale $\log N \cdot \log\log N$.

Together with the lower bound for all strong amplifiers, this is a tight dichotomy: strong amplification always costs an unbounded factor over $\log N$, but any unbounded factor suffices.

## Depends on

- [Amplifiers, strong amplifiers and initialization schemes](amplifiers-strong-amplifiers-and-initialization-schemes.md)
- [Strong amplification requires a slowdown](strong-amplification-requires-a-slowdown.md)

## Proof sketch

*Fixation.* Since $n \ll \ell$, the first mutant appears on a leaf with probability $\ell/N \to 1$. It is lost only when a hub resident fires out onto it, per step probability of order $1/(\alpha^3 N)$, while it fires into the hub with per step probability of order $1/(\alpha^2 N)$; so it seeds the hub about $\alpha(N)$ times before being lost. With fewer than $n/2$ hub mutants the hub dynamics are biased toward gaining mutants, so each seed reaches half the hub with constant probability, and some seed does so with high probability. A resident comeback must then convert back $n/2$ mutants of a well-mixed hub, which is exponentially unlikely.

*Time.* Split the process into active steps (the state changes) and waiting steps. A potential function $\psi$ increases by a constant in expectation per active step and attains each value at most $\alpha^2$ times in expectation; the maximal expected waiting times $W_k$ at potential level $k$ satisfy $\sum_k W_k \le N \log N \cdot \alpha^3$. The total expected number of steps is at most $\sum_k \alpha^2 W_k \le N \log N \cdot \alpha^5$, i.e. $\log N \cdot \alpha^5$ generations.

## Sources

- J. Tkadlec, A. Pavlogiannis, K. Chatterjee and M. A. Nowak, "Fast and strong amplifiers of natural selection", Nature Communications 12 (2021), article 4009, Results ("Selection reactors", Theorem 2, Eq. (4), Fig. 3) and Methods ("Fixation probability analysis", "Timescale analysis", Eqs. (7)–(9)); proofs in Supplementary Note 3, <https://doi.org/10.1038/s41467-021-24271-w>, PMCID PMC8242091.
