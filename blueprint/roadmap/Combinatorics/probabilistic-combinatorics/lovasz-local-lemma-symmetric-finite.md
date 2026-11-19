# Symmetric Lovász Local Lemma

Let $\Omega$ be a finite set with a probability mass function
$P$, that is, $P(\omega) \ge 0$ for every $\omega \in \Omega$ and
$\sum_{\omega \in \Omega} P(\omega) = 1$, and write $\Pr[E] = \sum_{\omega \in E} P(\omega)$ for
$E \subseteq \Omega$. Let $(A_i)_{i \in I}$ be a family of events indexed by a finite set $I$,
let $G$ be a simple graph on $I$ whose maximum degree is at most a natural number $d$, and let
$p \ge 0$ be a real number. Suppose that $\Pr[A_i] \le p$ for every $i \in I$, and that for every
$i \in I$ and every set $S \subseteq I$ containing neither $i$ nor any neighbour of $i$ in $G$,
$\Pr[A_i \cap \bigcap_{j \in S} A_j] = \Pr[A_i] \cdot \Pr[\bigcap_{j \in S} A_j]$.
If $e \cdot p \cdot (d + 1) \le 1$, then $\Pr[\bigcap_{i \in I} (\Omega \setminus A_i)] > 0$,
that is, with positive probability none of the events $A_i$ occurs.

The independence hypothesis, taken over all such $S$ (including $S = \emptyset$), says that
each $A_i$ is mutually independent of the family of events $A_j$ with $j$ neither $i$ nor a
neighbour of $i$.

## Background

- [Lovász local lemma, general form](lovasz-local-lemma-general-finite.md): the asymmetric criterion $\Pr[A_i] \le x_i \prod_{j \sim i}(1 - x_j)$, from which this symmetric case follows with $x_i = 1/(d+1)$ when $d \ge 1$, and with $x_i = p \le 1/e$ when $d = 0$.
- [Variance of a count of events with a dependency graph](first-and-second-moment-methods/variance-sum-indicator-le.md): the second moment method uses a dependency graph too, but needs only pairwise independence of non-adjacent events and shows that many events occur rather than none.

## Sources

- Noga Alon and Joel H. Spencer, The Probabilistic Method, third edition, Wiley, 2008, Corollary 5.1.2, for the criterion $e p (d + 1) \le 1$; the original local lemma of Paul Erdős and László Lovász (1975) gives the earlier weaker criterion $4 p d \le 1$.
