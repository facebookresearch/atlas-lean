# Deletion of low-degree vertices

Let $G$ be a graph on $\{0, \dots, n-1\}$ and $\beta, \Phi_0$ real numbers. For a vertex set $S$, write $\deg_S(v)$ for the number of neighbours of $v$ in $S$, $P(S) = \sum_{v \in S} \deg_S(v)$ for the number of ordered adjacent pairs in $S$, and $\Phi(S) = P(S) - \beta|S|(|S|+1)$. If $\Phi(S) \ge \Phi_0$, then $S$ contains a set $T$ with $\Phi(T) \ge \Phi_0$ on which every vertex $v$ satisfies $\deg_T(v) \ge \beta|T|$.

Proof: if some $v \in S$ has $\deg_S(v) < \beta|S|$, delete it. Then $P$ drops by $2\deg_S(v) < 2\beta|S|$ while $\beta|S|(|S|+1)$ drops by exactly $2\beta|S|$, so $\Phi$ increases. Strong induction on $|S|$ finishes the proof.

This is the deletion argument of Lemma 3.3.12 of the source, which tracks the edge count directly; the potential $\Phi$ is a reformulation of that count.

## Sources

- J. Noel, *Extremal Combinatorics* lecture notes (version of 15 Nov 2026), extremalcombinatorics.com, Lemma 3.3.12.
