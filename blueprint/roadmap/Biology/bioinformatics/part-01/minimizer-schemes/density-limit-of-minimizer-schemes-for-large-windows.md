# Density limit of minimizer schemes for large windows

Use the definitions of local schemes, minimizers schemes and density from [Universal sets and asymptotically optimal minimizer density](universal-sets-and-asymptotically-optimal-minimizer-density.md): $\Sigma$ has size $\sigma$, a minimizers scheme $f$ is given by a total order on $\Sigma^k$, and $d_{f,k,w}$ is its density for windows of $w$ consecutive $k$-mers.

**Proposition (monotonicity).** For any minimizers scheme $f$ and fixed $k$, the map $w \mapsto d_{f,k,w}$ is non-increasing.

**Proposition (floor).** For any minimizers scheme $f$, $d_{f,k,w} \ge \sigma^{-k}$ for all $w$.

**Theorem.** For any minimizers scheme $f$ and fixed $k$,

$$\lim_{w \to \infty} d_{f,k,w} = \sigma^{-k}.$$

Consequently the density factor $d_{f,k,w}\,(w+1)$ of every minimizers scheme grows at least linearly in $w$, whereas there exist **forward schemes** (local schemes whose selected positions are non-decreasing along the sequence) with density factor $O(\sqrt{w})$.

## Depends on

- [Universal sets and asymptotically optimal minimizer density](universal-sets-and-asymptotically-optimal-minimizer-density.md)

## Expansion

Monotonicity: on a de Bruijn sequence of order $w+k+1$, if the window of $w+1$ $k$-mers starting at $i$ selects a different $k$-mer than the window of $w$ $k$-mers starting at $i$, the new right-most $k$-mer at $i+w$ is smaller than all others, so it is also selected by the $w$-window starting at $i+1$; hence the selected set for $w+1$ is contained in that for $w$. Floor: the globally smallest $k$-mer $\mu$ is selected at every occurrence, and in a de Bruijn sequence of order $w+k$ it occurs $\sigma^w$ times among $\sigma^{w+k}$ positions. Limit: when $w \gg \sigma^k$ almost every window contains $\mu$, so almost every selected position is an occurrence of $\mu$; the order on the remaining $k$-mers becomes irrelevant. The $O(\sqrt{w})$ forward scheme applies a minimizers order on shorter $k'$-mers with $k' = \log_\sigma \sqrt{w}$, which still selects positions inside each window.

## Sources

- G. Marçais, D. DeBlasio, C. Kingsford, "Asymptotically optimal minimizers schemes", Bioinformatics 34(13) (2018) i13–i22, Propositions 5–7 and Theorem 2, <https://doi.org/10.1093/bioinformatics/bty258>, PMCID PMC6037127.
