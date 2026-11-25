# Sankoff's recursion at an internal vertex

For every internal node with edge costs $P, Q$ and children $l, r$, and every state $s$,

$$\mathrm{Sk}(t, s) = \min_{a} \bigl(P(s, a) + \mathrm{Sk}(l, a)\bigr) + \min_{b} \bigl(Q(s, b) + \mathrm{Sk}(r, b)\bigr),$$

where $\mathrm{Sk}$ is [Sankoff's cost](sankoff.md).
