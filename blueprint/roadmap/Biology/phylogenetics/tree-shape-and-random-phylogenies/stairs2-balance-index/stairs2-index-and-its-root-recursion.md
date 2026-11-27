# Stairs2 index and its root recursion

**Definition.** For a rooted binary tree $T$ with $n$ leaves, let $\mathring V(T)$ be its set of inner vertices, and for $v\in\mathring V(T)$ let $n_{v_1},n_{v_2}$ be the leaf numbers of the two maximal pending subtrees rooted at the children of $v$. The **stairs2 index** is $\mathrm{st}_2(T)=0$ if $n\in\{0,1\}$ and, for $n\ge2$,

$$\mathrm{st}_2(T)=\frac{1}{n-1}\sum_{v\in\mathring V(T)}\frac{\min\{n_{v_1},n_{v_2}\}}{\max\{n_{v_1},n_{v_2}\}}\in(0,1],$$

the mean ratio of smaller to larger subtree size over the $n-1$ inner vertices. It is a balance index: larger values mean more balanced trees.

**Lemma (root recursion).** If $n\ge2$ and $T=(T_1,T_2)$ is the standard decomposition at the root with $n_1\ge n_2$ leaves, then

$$\mathrm{st}_2(T)=\frac{(n_1-1)\,\mathrm{st}_2(T_1)+(n_2-1)\,\mathrm{st}_2(T_2)+\dfrac{n_2}{n_1}}{n_1+n_2-1},$$

with the convention that the formula also holds when $T_2$ is empty ($n_2=0$, $\mathrm{st}_2(T_2)=0$).

**Proposition (upper bound).** For every rooted binary tree with $n\ge2$ leaves, $\mathrm{st}_2(T)\le1$. When $n=2^h$, equality holds exactly for the fully balanced tree $T^{fb}_h$ of height $h$, in which every leaf has depth $h$. For example, the unique tree shape on $3$ leaves has inner-vertex ratios $1$ and $\tfrac12$, so $\mathrm{st}_2=\tfrac12(1+\tfrac12)=\tfrac34$.

## Proof sketch

The inner vertices of $T$ are the root together with the inner vertices of $T_1$ and $T_2$, of which there are $n_1-1$ and $n_2-1$; the root contributes the ratio $n_2/n_1$. Multiplying each subtree index by its number of inner vertices recovers its sum of ratios, and dividing by $n-1=n_1+n_2-1$ gives the recursion. Every ratio is at most $1$, so $\mathrm{st}_2\le1$, with equality iff every inner vertex splits its leaves evenly, which forces $n$ to be a power of two and the tree to be fully balanced.

## Sources

- Bryan Currie and Kristina Wicke, "On the maximum value of the stairs2 index", *Advances in Applied Mathematics* 159 (2024), 102732, <https://doi.org/10.1016/j.aam.2024.102732>. Preprint version: arXiv:2401.08838 (2024), Section 3, Definition 1, Lemma 1 and Proposition 1, <https://doi.org/10.48550/arXiv.2401.08838>.
