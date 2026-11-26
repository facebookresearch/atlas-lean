# Partial Iso

Let $n, m \in \mathbb{N}$ and let $R$ and $S$ be Boolean-valued binary relations on $\{0, \dots, n-1\}$ and $\{0, \dots, m-1\}$. A position is a finite list $P$ of pairs $(a, b)$ with $a < n$ and $b < m$. The position $P$ is a partial isomorphism between $R$ and $S$ if for all pairs $(a, b), (a', b') \in P$

$$a = a' \iff b = b' \qquad \text{and} \qquad R(a, a') = S(b, b').$$

The first condition says that the pairs match elements injectively in both directions; the second that $R$ and $S$ agree on corresponding pairs.
