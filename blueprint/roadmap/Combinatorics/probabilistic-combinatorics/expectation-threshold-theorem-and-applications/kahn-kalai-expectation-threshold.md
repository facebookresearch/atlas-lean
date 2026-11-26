# The Kahn-Kalai expectation threshold q(F)

Let $\mathcal{F} \subseteq 2^X$ be a nontrivial increasing family and $\mu_p$ the product measure with marginals $p$. A family $\mathcal{G} \subseteq 2^X$ *covers* $\mathcal{F}$ if every $F \in \mathcal{F}$ contains some $G \in \mathcal{G}$, i.e. $\mathcal{F} \subseteq \langle\mathcal{G}\rangle$. $\mathcal{F}$ is *$p$-small* if some cover satisfies $\sum_{G \in \mathcal{G}} p^{|G|} \le 1/2$. The *expectation threshold* is

$$
q(\mathcal{F}) = \max\{p : \mathcal{F} \text{ is } p\text{-small}\}.
$$

One has $q(\mathcal{F}) \le p_c(\mathcal{F})$ (next lemma) and $q(\mathcal{F}) \le q_f(\mathcal{F})$, where $q_f$ is the fractional expectation threshold.

## Depends on

- [The threshold $p_c(\mathcal F)$](../thresholds-and-expectation-thresholds/p-c.md)
- [The fractional expectation-threshold $q_f(\mathcal F)$](../thresholds-and-expectation-thresholds/q-f.md)
- [Weakly $p$-small families](../thresholds-and-expectation-thresholds/is-weakly-small.md)

## Sources

- Jeff Kahn, Gil Kalai, "Thresholds and expectation thresholds", Combinatorics, Probability and Computing 16(3) (2007).
- Michel Talagrand, "Are many small sets explicitly small?", STOC (2010).
- Jinyoung Park, Huy Tuan Pham, "A proof of the Kahn-Kalai conjecture", Journal of the AMS 37(1) (2024); arXiv:2203.17207.
