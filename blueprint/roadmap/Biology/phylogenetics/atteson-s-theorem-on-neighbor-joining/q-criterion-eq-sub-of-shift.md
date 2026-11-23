# The shifting lemma

Let $S$ be a finite set of clusters, $D, D'$ cluster dissimilarities and $f$ a real function on clusters such that $D'(s, s) = D(s, s)$ for $s \in S$ and $D'(s, t) = D(s, t) + f(s) + f(t)$ for distinct $s, t \in S$. Then for all distinct $a, b \in S$,

$$Q_{D'}(a, b) = Q_D(a, b) - 2 \sum_{c \in S} f(c),$$

where $Q$ is the [Q-criterion](../neighbor-joining/q-criterion.md) on $S$; in particular $D$ and $D'$ have the same minimizing pairs (Mihaescu, Levy & Pachter 2009, Lemma 4).

## Sources

- R. Mihaescu, D. Levy and L. Pachter, *Why neighbor-joining works*, Algorithmica 54 (2009), 1–24; arXiv:cs/0602041, Lemma 4.
