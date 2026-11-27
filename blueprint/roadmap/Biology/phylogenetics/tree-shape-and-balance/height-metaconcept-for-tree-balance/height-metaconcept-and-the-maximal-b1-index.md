# Height metaconcept for tree balance and the maximal B1 index

**Setting.** All trees are rooted tree shapes with no vertex of out-degree one (the source's convention, Section 2.1); with such vertices allowed, subdividing an edge raises heights and the maximizer statements below fail. Let $T$ be such a tree with $n$ leaves, root $\rho$ and inner vertices $\mathring V(T)$; for a vertex $v$, $T_v$ is the pending subtree rooted at $v$ and $h(T_v)$ its height (the number of edges on a longest path from $v$ to a leaf below it). The **height sequence** $\mathcal H(T)$ lists the heights $h(T_v)$, $v\in\mathring V(T)$, in increasing order (it has $n-1$ entries when $T$ is binary). For a function $f:\mathbb N_{\ge1}\to\mathbb R$, the **height metaconcept** is

$$\Phi^{\mathcal H}_f(T)=\sum_{v\in\mathring V(T)} f\bigl(h(T_v)\bigr),$$

which satisfies the recursion $\Phi^{\mathcal H}_f(T)=\sum_{i=1}^k\Phi^{\mathcal H}_f(T_i)+f(\max_i h_i+1)$ for $T=(T_1,\dots,T_k)$ with subtree heights $h_i$ (Proposition 3.24). Shao and Sokal's **$B_1$ index** is $B_1(T)=\sum_{v\in\mathring V(T)\setminus\{\rho\}}1/h(T_v)$. The *greedy-from-the-bottom tree* $T^{gfb}_n$ is the binary tree obtained by starting from $n$ single vertices and repeatedly joining two trees of minimal leaf number; write $n=2^{h_n}+p_n$ with $h_n=\lfloor\log_2 n\rfloor$ and $0\le p_n<2^{h_n}$. An imbalance index is a function minimized exactly by the most balanced trees and maximized by the caterpillar $T^{cat}_n$.

**Theorem 3.2.** $\Phi^{\mathcal H}_f$ is an imbalance index on rooted trees whenever $f$ is strictly increasing and *1-positive* ($f(x)>0$ for all $x\ge1$), and a binary imbalance index whenever $f$ is strictly increasing. For strictly increasing 1-positive $f$ the caterpillar is the unique maximizer over all rooted trees, with value $\sum_{i=1}^{n-1}f(i)$ (Theorem 3.4, Corollary 3.20).

**Theorem 3.3 (minimizers).** Among rooted binary trees with $n$ leaves:
1. $T^{gfb}_n$ minimizes $\Phi^{\mathcal H}_f$ for every increasing $f$; indeed $\mathcal H(T^{gfb}_n)_i\le\mathcal H(T)_i$ for all $i$ and all binary $T$.
2. Every tree minimizing $\Phi^{\mathcal H}_f$ for all increasing $f$ has the same height sequence as $T^{gfb}_n$ and minimal height $\lceil\log_2 n\rceil$, and a minimizer for one strictly increasing $f$ is a minimizer for all increasing $f$.
3. Every pending subtree of such a minimizer is itself a minimizer for its own leaf number.

$T^{gfb}_n$ is the unique minimizer for strictly increasing $f$ if and only if $n=2^h-2^i$ for integers $h>i\ge0$ (Proposition 3.15). The minimum value is $\sum_{i=1}^{h_n}2^{h_n-i}f(i)$ when $p_n=0$ and $\sum_{i=1}^{h_n+1}\bigl(2^{h_n+1-i}-\lceil(2^{h_n}-p_n-2^{i-1}+1)/2^i\rceil\bigr)f(i)$ otherwise (Corollary 3.22).

**Theorem 3.25 ($B_1$ maximizers).** The trees maximizing $B_1$ among all rooted trees with $n$ leaves are exactly the binary trees minimizing $\Phi^{\mathcal H}_f$ for all increasing $f$. In particular they are binary, $T^{gfb}_n$ is always one of them, the maximizer is unique if and only if $n=2^h-2^i$ ($h>i\ge0$), and for odd $n$ it is unique if and only if $n=2^h-1$. The maximal value is $\sum_{i=1}^{h_n-1}2^{h_n-i}/i$ if $p_n=0$ and $\sum_{i=1}^{h_n}\bigl(2^{h_n+1-i}-\lceil(2^{h_n}-p_n-2^{i-1}+1)/2^i\rceil\bigr)/i$ otherwise (Corollary 3.26).

## Expansion

Because $\Phi^{\mathcal H}_f$ is a sum of $f$ over the height sequence, a tree whose sorted height sequence is entrywise smallest minimizes it for every increasing $f$ at once. Greedy clustering of the smallest trees keeps every pending-subtree height as low as possible, which gives the entrywise minimality of $\mathcal H(T^{gfb}_n)$. The $B_1$ index is $-\Phi^{\mathcal H}_g$ for the increasing function $g(x)=-1/x$, up to the root term $1/h(T)$, which is constant ($=1/\lceil\log_2 n\rceil$) on the minimizers; this links $B_1$ maximization to height-metaconcept minimization. Uniqueness for $n=2^h-2^i$ comes from the fact that only then is the height sequence realized by a single tree shape.

## Depends on

- [GFB trees minimize concave subtree-size indices](../greedy-from-the-bottom-trees/gfb-trees-minimize-concave-subtree-size-indices.md)

## Sources

- M. Fischer, T. N. Hamann, K. Wicke, "A height-based metaconcept for rooted tree balance and its implications for the $B_1$ index", *Advances in Applied Mathematics* 182 (2027), 103158, Theorem 3.2, Theorem 3.3, Theorem 3.4, Proposition 3.15, Corollary 3.20, Corollary 3.22, Proposition 3.24, Theorem 3.25, Corollary 3.26, <https://doi.org/10.1016/j.aam.2026.103158> (preprint arXiv:2601.15219).
