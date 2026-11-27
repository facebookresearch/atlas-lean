# Set alignment problem for label-ordered paths

**Problem.** Let $S_1,\dots,S_n$ and $P_1,\dots,P_m$ be two ordered sequences of sets over a label universe $L$ such that every label lies in exactly one $S_i$ and exactly one $P_j$; write $f(u) = i$ and $g(u) = j$ for the indices of $u$. Find a largest set $A\subseteq L$ that is **order-consistent**, meaning that no two of its labels appear in strictly opposite orders:

$$\big(f(a)-f(b)\big)\big(g(a)-g(b)\big)\ge 0\qquad\text{for all } a, b\in A.$$

This is the maximum common tree problem for two multi-labeled trees that are both paths (vertices $v_1,\dots,v_n$ with label sets $S_i$ and $w_1,\dots,w_m$ with label sets $P_j$): labels kept in a common path must not appear in opposite ancestral orders, and labels sharing a vertex in one path may be split over several vertices of the common path in either order. The source states the condition as $f(a)\le f(b)\iff g(a)\le g(b)$; that stronger condition forbids, for instance, $S_1 = \{a,b\}$, $P_1 = \{a\}$, $P_2 = \{b\}$ from keeping both labels, whereas the recurrence below keeps both, so the page states the condition the recurrence computes.

**Recurrence.** Let $D(i,j)$ be the optimum for the prefixes $(S_1,\dots,S_i)$ and $(P_1,\dots,P_j)$. Then

$$D(i,0) = D(0,j) = 0,\qquad D(i,j) = \max\big(D(i,j-1),\,D(i-1,j)\big) + |S_i\cap P_j|\quad (i,j\ge 1).$$

**Complexity.** All intersection sizes $|S_i\cap P_j|$ can be tabulated in $O\big(\sum_i|S_i| + \sum_j|P_j| + nm\big)$ time and space by hashing $u\mapsto (f(u), g(u))$ and incrementing a counter per label, so the set alignment problem is solvable in the same time and space.

## Expansion

A set is order-consistent exactly when its points $(f(u), g(u))$ form a chain in the product order on $\{1,\dots,n\}\times\{1,\dots,m\}$, so the optimum is the largest total weight $|S_i\cap P_j|$ collected by a monotone lattice path through the cells. Lower bound: adding all of $S_i\cap P_j$ to an optimal solution for $(i,j-1)$ or $(i-1,j)$ stays order-consistent, because the point $(i,j)$ is $\ge$ every point of that solution in both coordinates. Upper bound: split an optimal $A(i,j)$ into $A(i,j)\setminus(S_i\cap P_j)$ and $S_i\cap P_j$; a label of the remainder in $S_i$ (so $g < j$) and one in $P_j$ (so $f < i$) would be in strictly opposite orders, so the remainder misses $S_i$ or misses $P_j$ and is a feasible solution for $(i-1,j)$ or $(i,j-1)$. The recurrence is that of a heaviest monotone lattice path with cell weights $|S_i\cap P_j|$; the weighted longest-common-subsequence recurrence, with a diagonal step, would compute the source's "iff" condition instead.

## Sources

- N. Karpov, S. Malikic, M. K. Rahman, S. C. Sahinalp, *A multi-labeled tree dissimilarity measure for comparing "clonal trees" of tumor progression*, Algorithms for Molecular Biology 14 (2019), 17, section "Set alignment problem" (Lemma 1, Observation 1, Lemma 2). <https://doi.org/10.1186/s13015-019-0152-9> (PMCID: PMC6661107)
