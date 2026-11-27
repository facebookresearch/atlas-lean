# Blockwise q-gram distance and optimal rotation

**Setting.** Strings are arrays $x[0..m-1]$ over a fixed alphabet $\Sigma$ with $|\Sigma| = O(1)$. The $i$-th rotation of $x$ is $x^{(i)} = x[i..m-1]\,x[0..i-1]$. For $q > 0$ the **$q$-gram profile** $G_q(x)$ is the vector indexed by $v \in \Sigma^q$ whose entry is the number of occurrences of $v$ in $x$, and the **$q$-gram distance** is

$$D_q(x,y) = \sum_{v \in \Sigma^q} \bigl| G_q(x)[v] - G_q(y)[v] \bigr| .$$

It is a pseudometric: non-negative, symmetric and satisfies the triangle inequality, but distinct strings may have distance $0$.

**Definition (blockwise $q$-gram distance).** Let $|x| = m \le n = |y|$ and $\beta \ge 1$, with $m$ and $n$ multiples of $\beta$. Cut $x$ into $\beta$ consecutive blocks of length $m/\beta$ and $y$ into $\beta$ blocks of length $n/\beta$, and set

$$D_{\beta,q}(x,y) = \sum_{j=0}^{\beta-1} D_q\!\left(x\!\left[\tfrac{jm}{\beta} .. \tfrac{(j+1)m}{\beta}-1\right],\ y\!\left[\tfrac{jn}{\beta} .. \tfrac{(j+1)n}{\beta}-1\right]\right).$$

$\beta = 1$ recovers $D_q$; larger $\beta$ forces $q$-grams to match in roughly the same region, restoring some of the locality an alignment would have.

**Circular sequence comparison (CSC).** Given $x$, $y$ with $m \le n$, $\beta \ge 1$ and $q < m$, find a rotation index $i \in \{0,\dots,m-1\}$ minimizing $D_{\beta,q}(x^{(i)}, y)$.

**Lemma 2.** With $O(|\Sigma|^q)$ space available, $D_{\beta,q}(x,y)$ can be computed in $O(m+n)$ time and $O((m+n)/\beta)$ extra space.

**Lemma 3 (naive algorithm).** Evaluating $D_{\beta,q}(x'[i..i+m-1], y)$ for $x' = xx$ and every $0 \le i < m$ solves CSC in $O(m(m+n))$ time and $O((m+n)/\beta)$ extra space.

**Theorem 1 (suffix-array algorithm).** CSC can be solved exactly in $O(\beta m + n)$ time and space.

## Expansion

Lemma 2 applies the linear-time $q$-gram distance computation to each of the $\beta$ block pairs in turn, so the extra space is that of one pair of blocks of lengths $m/\beta$ and $n/\beta$. For Theorem 1, build the suffix array and LCP array of $xxy$ in linear time and use them to replace every $q$-gram of $x' = xx$ and $y$ by its rank among distinct $q$-grams, so each $q$-gram becomes a single integer letter. For $\beta = 1$, keep a difference vector $\mathrm{diff} = P(y) - P(\text{window})$ of rank counts between $y$ and the current length-$m$ window of $x'$, together with the running distance $\delta_i = \sum |\mathrm{diff}|$. Shifting the window by one position removes one rank and adds one rank, so $\mathrm{diff}$ changes in two coordinates and $\delta_{i+1}$ is $\delta_i \pm 1 \pm 1$ according to the signs of those coordinates before the update: $O(1)$ per shift, $O(m+n)$ overall. For general $\beta$, one window per block is maintained and each shift moves one $q$-gram across each of the $\beta$ block boundaries, costing $O(\beta)$ per shift.

The blockwise distance is a filter: in experiments on mitochondrial DNA, the rotation it selects, refined by aligning the end blocks, is close to the rotation chosen by exhaustive Needleman–Wunsch alignment of all rotations at a fraction of the cost.

## Depends on

- [q-gram (seed) filtering lemma for approximate matching](../../q-gram-filtering-lemma-for-approximate-matching.md)

## Sources

- R. Grossi, C. S. Iliopoulos, R. Mercas, N. Pisanti, S. P. Pissis, A. Retha, F. Vayani, "Circular sequence comparison: algorithms and applications", Algorithms for Molecular Biology 11 (2016) 12, Definition 1, Lemmas 1–3 and Theorem 1, <https://doi.org/10.1186/s13015-016-0076-6>, PMCID PMC4862142.
