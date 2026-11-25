# Matroid intersection by augmenting paths

Let $M_1 = (S, \mathcal I_1)$ and $M_2 = (S, \mathcal I_2)$ be matroids on a common finite ground set $S$, given by independence oracles, with rank functions $r_1$ and $r_2$. For a common independent set $I \in \mathcal I_1 \cap \mathcal I_2$, the *exchange graph* $D(I)$ is the directed bipartite graph on $I$ and $S \setminus I$ with these arcs, for $y \in I$ and $x \notin I$:
- an arc $y \to x$ whenever $I - y + x \in \mathcal I_1$;
- an arc $x \to y$ whenever $I - y + x \in \mathcal I_2$.

Let $X_1 = \{x \notin I : I + x \in \mathcal I_1\}$ and $X_2 = \{x \notin I : I + x \in \mathcal I_2\}$.

**Algorithm.** Start with $I = \emptyset$ and repeat:
- if $D(I)$ has a path from $X_1$ to $X_2$, take one with no shortcuts, for example a shortest one, and replace $I$ by the symmetric difference $I \triangle P$ with its vertex set $P$;
- otherwise stop, and output $I$ together with $U = \{z \in S : z \text{ can reach } X_2 \text{ in } D(I)\}$.

**Theorem.**
1. Each augmentation yields a common independent set of size $|I| + 1$.
2. At termination, $|I| = r_1(U) + r_2(S \setminus U)$. Since every common independent set $J$ has $|J| \le r_1(U) + r_2(S \setminus U)$, as in [Edmonds' min-max formula](../../Combinatorics/matroid-theory/matroid-intersection-theorem/edmonds-matroid-intersection.md), $I$ is a maximum common independent set.
3. With $r = \max(r_1(S), r_2(S))$ and $n = |S|$, the algorithm uses $O(r^2 n)$ oracle calls. Always choosing shortest augmenting paths reduces this to $O(r^{1.5} n)$ (Cunningham).

**Proof.**
1. Add a new element $t$ that is independent of everything. In the single-matroid exchange graph of $M_1$, the arcs of $P$ together with an arc from $t$ to the first vertex form a perfect matching between $(I \cap P) + t$ and $P \setminus I$. Because $P$ has no shortcuts, this matching is unique, and a unique perfect matching certifies that $(I + t) \triangle P$ is independent. So $I \triangle P \in \mathcal I_1$. The same argument, matching $t$ to the last vertex, gives $I \triangle P \in \mathcal I_2$.
2. At termination, $X_2 \subseteq U$ and $X_1 \cap U = \emptyset$. If $|I \cap U| < r_1(U)$, some $x \in U \setminus I$ has $(I \cap U) + x \in \mathcal I_1$. Then some $y \in I \setminus U$ has $I - y + x \in \mathcal I_1$, and the arc $y \to x$ puts $y$ in $U$, a contradiction. Symmetrically, $|I \setminus U| = r_2(S \setminus U)$.
3. There are at most $r$ augmentations. Each builds $D(I)$ with $O(rn)$ oracle calls and searches it in $O(rn)$ time.

## Proof depends on

- [Edmonds' matroid intersection theorem](../../Combinatorics/matroid-theory/matroid-intersection-theorem/edmonds-matroid-intersection.md)

## Background

- [Matroid greedy algorithm](matroid-greedy-algorithm/README.md)

## Sources

- M. X. Goemans, *18.438 Advanced Combinatorial Optimization*, Lecture 11 "Matroid intersection" (scribe notes, 22 October 2009), MIT, <https://math.mit.edu/~goemans/18438F09/lec11.pdf>:
    - Lemma 1: strong basis exchange;
    - Theorem 4: the min-max formula;
    - Definition 3: the exchange graph $D_{M_1,M_2}(I)$, the sets $X_1$ and $X_2$, augmenting paths without shortcuts, and the set $U$ of vertices that can reach $X_2$;
    - the proofs that the final $I$ and $U$ attain equality and that $I \triangle P$ is common independent;
    - Section 4: $O(r^2 n)$ oracle calls;
    - Remark 1: Cunningham's $O(r^{1.5} n)$ bound with shortest augmenting paths.
