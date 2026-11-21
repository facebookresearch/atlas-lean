# Brute-force likelihood factors over subtrees

For every internal node $t$ with weights $P, Q$ and children $l, r$, and every state $s$,

$$\Lambda(t, s) = \Bigl(\sum_{a} P(s, a)\, \Lambda(l, a)\Bigr) \Bigl(\sum_{b} Q(s, b)\, \Lambda(r, b)\Bigr),$$

where $\Lambda$ is the [brute-force likelihood](brute-lik.md).
