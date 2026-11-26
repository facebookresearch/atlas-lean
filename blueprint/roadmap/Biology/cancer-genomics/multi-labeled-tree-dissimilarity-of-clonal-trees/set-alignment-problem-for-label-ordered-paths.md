# Set alignment problem for label-ordered paths

**Problem.** Let $S_1,\dots,S_n$ and $P_1,\dots,P_m$ be two ordered sequences of sets over a label universe $L$ such that every label lies in exactly one $S_i$ and exactly one $P_j$; write $f(u) = i$ and $g(u) = j$ for the indices of $u$. Find a largest set $A\subseteq L$ that is **order-consistent**:

$$f(a)\le f(b)\iff g(a)\le g(b)\qquad\text{for all } a, b\in A.$$

This is the maximum common tree problem for two multi-labeled trees that are both paths (vertices $v_1,\dots,v_n$ with label sets $S_i$ and $w_1,\dots,w_m$ with label sets $P_j$): labels kept in a common path must appear in the same ancestral order in both.

**Recurrence.** Let $D(i,j)$ be the optimum for the prefixes $(S_1,\dots,S_i)$ and $(P_1,\dots,P_j)$. Then

$$D(i,0) = D(0,j) = 0,\qquad D(i,j) = \max\big(D(i,j-1),\,D(i-1,j)\big) + |S_i\cap P_j|\quad (i,j\ge 1).$$

**Complexity.** All intersection sizes $|S_i\cap P_j|$ can be tabulated in $O\big(\sum_i|S_i| + \sum_j|P_j| + nm\big)$ time and space by hashing $u\mapsto (f(u), g(u))$ and incrementing a counter per label, so the set alignment problem is solvable in the same time and space.

## Expansion

Lower bound: adding all of $S_i\cap P_j$ to an optimal solution for $(i,j-1)$ or $(i-1,j)$ stays order-consistent, because the new labels have the largest index in both orders. Upper bound: split an optimal $A(i,j)$ into $A(i,j)\setminus(S_i\cap P_j)$ and $S_i\cap P_j$; order consistency forbids the remainder from meeting both $S_i$ and $P_j$, so it is a feasible solution for $(i,j-1)$ or $(i-1,j)$. The recurrence is the longest-common-subsequence recurrence with set intersections as weights.

## Sources

- N. Karpov, S. Malikic, M. K. Rahman, S. C. Sahinalp, *A multi-labeled tree dissimilarity measure for comparing "clonal trees" of tumor progression*, Algorithms for Molecular Biology 14 (2019), 17, Methods, "Set alignment problem" (Lemma 1, Observation 1, Lemma 2). <https://doi.org/10.1186/s13015-019-0152-9> (PMCID: PMC6661107)
