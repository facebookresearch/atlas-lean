# Sign-constrained three-segment breakpoint segmentation

**Setting.** Two synteny blocks $A$ and $B$ are consecutive on a reference genome but not on a compared genome. The region $S_r$ between them is aligned locally against the sequences $S_{oA}$ and $S_{oB}$ flanking the orthologues of $A$ and $B$ in the compared genome. Each position of $S_r$ covered by at least one hit is coded $I_k = 1$ if covered only by hits from $S_{oA}$, $I_k = -1$ if covered only by hits from $S_{oB}$, and $I_k = 0$ if covered by both; uncovered positions are dropped, giving $I \in \{-1,0,1\}^n$.

**Model.** For change points $0 \le u_1 \le u_2 \le n$ fit a piecewise constant function with values $\mu_1, \mu_2, \mu_3$ on $[1,u_1]$, $(u_1,u_2]$, $(u_2,n]$ by minimizing

$$f(u_1,u_2) = \sum_{k=1}^{u_1}(I_k-\mu_1)^2 + \sum_{k=u_1+1}^{u_2} I_k^2 + \sum_{k=u_2+1}^{n}(I_k-\mu_3)^2,$$

where $\mu_2 = 0$ (the refined breakpoint), $\mu_1$ is the mean of the first segment if that mean is positive and $+\infty$ otherwise, and $\mu_3$ is the mean of the last segment if it is negative and $+\infty$ otherwise; empty end segments contribute $0$.

**Theorem.** Let $P(u) = \sum_{k \le u} I_k$ and $Q(u) = \sum_{k > u} I_k$, and set

$$g_1(u) = \begin{cases} P(u)^2/u & P(u) > 0 \\ 0 & u = 0 \\ -\infty & \text{otherwise}\end{cases}, \qquad g_3(u) = \begin{cases} Q(u)^2/(n-u) & Q(u) < 0 \\ 0 & u = n \\ -\infty & \text{otherwise.}\end{cases}$$

Then $f(u_1,u_2) = \sum_k I_k^2 - g_1(u_1) - g_3(u_2)$, every maximizer $x_1$ of $g_1$ and every maximizer $x_2$ of $g_3$ satisfy $x_1 \le x_2$, and $(x_1, x_2)$ minimizes $f$ over $0 \le u_1 \le u_2 \le n$. Hence the optimal segmentation is found in $O(n)$ time by two independent scans, instead of the $O(n^2)$ scan or dynamic programme over all pairs.

## Expansion

Expanding the squares with $\mu_1 = P(u_1)/u_1$ and $\mu_3 = Q(u_2)/(n-u_2)$ gives the decomposition, and the two terms involve different variables. For non-crossing, suppose $x_1 > x_2$ and let $b = \sum_{x_2 < k \le x_1} I_k$. If $b \ge 0$ then $Q(x_1) = Q(x_2) - b \le Q(x_2) < 0$ and $n - x_1 < n - x_2$, so $g_3(x_1) > g_3(x_2)$. If $b<0$ then $P(x_2) = P(x_1) - b > P(x_1) > 0$ and $x_2 < x_1$, so $g_1(x_2) > g_1(x_1)$. Either way one of them is not a maximizer. The paper states this lemma with the prefix and suffix means $P(u)/u$ and $Q(u)/(n-u)$ as the quantities to optimize; the decomposition shows that the quantities to optimize are $P(u)^2/u$ and $Q(u)^2/(n-u)$, i.e. the mean weighted by segment length, and the non-crossing argument goes through unchanged. Significance of the fitted three-segment structure is assessed by a permutation test that shuffles runs of identical values (hit blocks) rather than single positions.

## Sources

- C. Lemaitre, E. Tannier, C. Gautier, M.-F. Sagot, "Precise detection of rearrangement breakpoints in mammalian chromosomes", BMC Bioinformatics (2008), Methods: refining the breakpoints, segmentation (Eq. (1)), speed-up (Lemma 1), statistical test, <https://doi.org/10.1186/1471-2105-9-286>, PMCID PMC2443379.
