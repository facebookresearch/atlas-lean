# Encoding bound for cell samples

Let a static cell-probe structure store a random input $D$ in $S$ cells of $w$ bits, let $C = C(D)$ be a set of $\Delta$ of its cells chosen as a function of $D$, and let $A$ be the answers, on $D$, of the queries resolved by $C$. If $H(D \mid A) \le H(D) - k$, then $\Delta(w + \lceil \log_2 S \rceil) \ge k$. Combined with the cell-sampling lemma, a lower bound $t$ follows whenever resolving $|\mathcal{Q}|(\Delta/2S)^t$ queries would reveal more than $\Delta(w + \log_2 S)$ bits about $D$.

## Proof sketch

Let $Y$ be the list of addresses and contents of the cells of $C$, a string of exactly $\Delta(w + \lceil\log_2 S\rceil)$ bits. Simulating every query on $Y$ and discarding those that request a cell outside $C$ recovers $A$ from $Y$, so $H(D \mid Y) \le H(D \mid A) \le H(D) - k$. Hence $k \le H(D) - H(D \mid Y) = I(D; Y) \le H(Y) \le \Delta(w + \lceil\log_2 S\rceil)$. Larsen phrases the same count as an encoding of $D$ by $Y$ followed by an optimal code for $D$ given $Y$, compared with $H(D)$ via Shannon's source coding theorem.

## Depends on

- [Static cell-probe structure with space $S$ and query time $t$](static-cell-probe-structure.md)

## Proof depends on

- [Cell-sampling lemma](cell-sampling-lemma.md)

## Sources

- Kasper Green Larsen, "Higher Cell Probe Lower Bounds for Evaluating Polynomials", FOCS (2012).
- Rina Panigrahy, Kunal Talwar, Udi Wieder, "Lower Bounds on Near Neighbor Search via Metric Expansion", FOCS (2010), arXiv:1005.0418.
