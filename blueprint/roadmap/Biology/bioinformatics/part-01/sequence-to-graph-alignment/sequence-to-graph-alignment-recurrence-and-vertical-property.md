# Sequence-to-graph alignment recurrence and the vertical property

A **sequence graph** is a triple $G = (V, E, \sigma)$ with a finite node set $V = \{v_1, \dots, v_n\}$, directed edges $E \subseteq V \times V$ and a labelling $\sigma : V \to \Sigma$ assigning one letter to each node; $\delta_i^{\mathrm{in}}$ and $\delta_i^{\mathrm{out}}$ are the index sets of in- and out-neighbours of $v_i$. A **path** $p = (p_1, \dots, p_k)$ has $(p_i, p_{i+1}) \in E$ and may revisit nodes; its **path sequence** is $\sigma(p) = \sigma(p_1)\cdots\sigma(p_k)$. Fix a query $s \in \Sigma^*$ with $|s| = m$.

- **Sequence-to-graph matching (SGM):** find all paths $p$ with $\sigma(p) = s$.
- **Unit-cost semi-global sequence-to-graph alignment (SGA):** find a path $p$ minimizing the edit distance $d(\sigma(p), s)$.

For SGA let $C_{i,j}$ be the minimum of $d(\sigma(p), s[1..j])$ over paths $p$ ending at $v_i$. It satisfies the recurrence

$$C_{i,j} = \min\Big\{\ \min_{k \in \delta_i^{\mathrm{in}}} \big(C_{k,j-1} + \Delta_{i,j}\big),\ \ \min_{k \in \delta_i^{\mathrm{in}}} \big(C_{k,j} + 1\big),\ \ C_{i,j-1} + 1 \Big\}$$

with boundary $C_{i,1} = \Delta_{i,1}$, where $\Delta_{i,j} = 0$ if $\sigma(v_i) = s_j$ and $1$ otherwise. The three terms are the diagonal (match or mismatch), horizontal (graph letter deleted) and vertical (query letter inserted) moves. Despite the cyclic dependencies when $G$ has cycles, the recurrence has a unique solution, computable cell by cell in $O(|V| + m|E|)$ time.

**Theorem (vertical property).** For all $i$ and all $2 \le j \le m$,

$$C_{i,j} - C_{i,j-1} \in \{-1, 0, 1\}.$$

This is what allows a column of the DP matrix (one node, all $m$ query rows) to be stored, as in Myers' algorithm for strings, by the bottom score and two $m$-bit vectors $VP$, $VN$ of $+1$ and $-1$ vertical differences, with $C_{i,j} = \mathrm{popcount}(VP_{0..j}) - \mathrm{popcount}(VN_{0..j})$; one edge is then processed in $O(\lceil m/w \rceil)$ word operations for machine word size $w$. On a DAG, processing nodes in topological order and merging the columns of several in-neighbours by a row-wise minimum (computable in $O(\lceil m/w\rceil \log w)$ time) gives SGA in $O(|V| + \lceil m/w\rceil |E| \log w)$ time. The analogous extension of Shift-And solves SGM in $O(|V| + \lceil m/w\rceil |E|)$ time on DAGs (states from several in-neighbours are merged by bitwise OR) and in $O(|V| + m|E|)$ time on general graphs by re-propagating changed states until none change.

## Depends on

- [Unit-cost edit distance is a Needleman–Wunsch instance](../../sequence-alignment/pairwise-sequence-alignment/edit-distance-distance-eq-neg-nw-score.md)

## Expansion

The upper bound $C_{i,j} \le C_{i,j-1} + 1$ is the vertical term: append $s_j$ as an insertion. For the lower bound take an optimal alignment of $s[1..j]$ with $\sigma(p)$, $p$ ending at $v_i$, and remove $s_j$ from it. If $s_j$ was an inserted letter, its column disappears and the cost drops by one; if $s_j$ was aligned to a graph letter at cost $\Delta \in \{0, 1\}$, that column becomes a deletion of the graph letter at cost $1$. Either way one obtains an alignment of $s[1..j-1]$ with the same path at cost at most $C_{i,j} + 1$, so $C_{i,j-1} \le C_{i,j} + 1$. The published proof is arranged so that it does not presuppose that the scores were already computed correctly, which the bit-vector algorithm needs because it relies on the property while computing.

## Sources

- M. Rautiainen, V. Mäkinen and T. Marschall, "Bit-parallel sequence-to-graph alignment", Bioinformatics 35(19) (2019), 3599–3607, Section 2 (Definitions 1–2, Problems 1–2), Section 3 (Algorithm 1), Section 4 (Definition 3, Recurrence (1), Theorem 1, Section 4.2), <https://doi.org/10.1093/bioinformatics/btz162> (PMC6761980).
