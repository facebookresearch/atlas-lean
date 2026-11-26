# Encoding bound for cell samples

Suppose that for a random input $D$ with entropy $H(D)$, and for every set $C$ of $\Delta$ cells, the answers to the queries resolved by $C$ determine $D$ up to a remaining entropy of at most $H(D) - k$. Then $\Delta(w + \lceil \log_2 S \rceil) \ge k$. Combined with the cell-sampling lemma, a lower bound $t$ follows whenever resolving $|\mathcal{Q}|(\Delta/2S)^t$ queries would reveal more than $\Delta(w + \log_2 S)$ bits about $D$.

## Proof sketch

Encode $D$ by the addresses and contents of the cells of $C$, using $\Delta(w + \lceil\log_2 S\rceil)$ bits, followed by an optimal code for $D$ given the resolved answers, of expected length at most $H(D) - k + 1$. Since no prefix code beats the entropy, $\Delta(w + \lceil \log_2 S \rceil) + H(D) - k + 1 \ge H(D)$; integrality and averaging remove the additive one.

## Depends on

- [Static cell-probe structure with space $S$ and query time $t$](static-cell-probe-structure.md)

## Proof depends on

- [Cell-sampling lemma](cell-sampling-lemma.md)

## Sources

- Kasper Green Larsen, "Higher Cell Probe Lower Bounds for Evaluating Polynomials", FOCS (2012).
- Rina Panigrahy, Kunal Talwar, Udi Wieder, "Lower Bounds on Near Neighbor Search via Metric Expansion", FOCS (2010), arXiv:1005.0418.
