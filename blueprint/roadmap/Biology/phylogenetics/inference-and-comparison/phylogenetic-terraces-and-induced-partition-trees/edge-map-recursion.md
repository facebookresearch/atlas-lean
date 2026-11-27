# Post-order recursion for the edge map

Let $T$ be an unrooted binary tree on $X$ and $Y_i \subseteq X$ a partition species set, with [edge map](induced-partition-tree-edge-map.md) $f_i$.

**Theorem.** The edge map satisfies the following recursion, which determines it from the pendant edges inwards.

1. (External edges.) For a pendant edge $e = \{x\} \mid X \setminus \{x\}$,

$$f_i(e) = \begin{cases} \{x\} \mid Y_i \setminus \{x\}, & x \in Y_i,\\ \epsilon, & x \notin Y_i.\end{cases}$$

2. (Internal edges.) Let $e$ be an internal edge with two adjacent edges $e_1, e_2$ on one side, so that $e_1 = A \mid (B \cup C)$, $e_2 = B \mid (A \cup C)$ and $e = (A \cup B) \mid C$ for a partition $X = A \sqcup B \sqcup C$ into nonempty sets. Then

$$f_i(e) = \begin{cases} \epsilon, & f_i(e_1) = f_i(e_2),\\ f_i(e_1), & f_i(e_1) \neq \epsilon,\ f_i(e_2) = \epsilon,\\ f_i(e_2), & f_i(e_1) = \epsilon,\ f_i(e_2) \neq \epsilon,\\ e_i^{*}, & f_i(e_1) \neq f_i(e_2),\ \text{both} \neq \epsilon,\end{cases}$$

where $e_i^{*}$ is the unique edge of $T|_{Y_i}$ incident to both $f_i(e_1)$ and $f_i(e_2)$.

Consequently a single post-order traversal computes $f_i$ in time linear in $n$, the whole collection $F = \{f_1, \dots, f_k\}$ in time $O(nk)$, and the value $f_i(e)$ computed from either side of $e$ is the same.

## Depends on

- [Induced partition tree and the edge map of a supermatrix](induced-partition-tree-edge-map.md)

## Proof sketch

Statement 1 is the definition applied to the split $\{x\} \mid X \setminus \{x\}$. For statement 2 write the three restrictions $A \cap Y_i$, $B \cap Y_i$, $C \cap Y_i$ and read the definition off each case. If $f_i(e_1) = f_i(e_2) = \epsilon$, at least two of the three restrictions are empty, so one side of $e$ restricts to the empty set and $f_i(e) = \epsilon$. If $f_i(e_1) = f_i(e_2) \neq \epsilon$ then $A \cap Y_i = (A \cup C) \cap Y_i$ and $B \cap Y_i = (B \cup C) \cap Y_i$, forcing $C \cap Y_i = \emptyset$ and again $f_i(e) = \epsilon$. If $f_i(e_1) \neq \epsilon$ and $f_i(e_2) = \epsilon$ then $A \cap Y_i \neq \emptyset$, hence $(A \cup C) \cap Y_i \neq \emptyset$, so $B \cap Y_i = \emptyset$ and $C \cap Y_i \neq \emptyset$; therefore $f_i(e) = (A \cup B) \cap Y_i \mid C \cap Y_i = A \cap Y_i \mid (B \cup C) \cap Y_i = f_i(e_1)$, and symmetrically in the third case. In the last case all three restrictions are nonempty, so $f_i(e) \neq \epsilon$ and the split $(A \cup B) \cap Y_i \mid C \cap Y_i$ is displayed by the edge of $T|_{Y_i}$ adjacent to both $f_i(e_1)$ and $f_i(e_2)$.

## Sources

- O. Chernomor, A. von Haeseler and B. Q. Minh, "Terrace aware data structure for phylogenomic inference from supermatrices", Systematic Biology 65 (2016), 997–1008, Eqs. (3)–(4) and Appendix 1 (correctness of Eq. (4)), <https://doi.org/10.1093/sysbio/syw037>, PMCID: PMC5066062.
