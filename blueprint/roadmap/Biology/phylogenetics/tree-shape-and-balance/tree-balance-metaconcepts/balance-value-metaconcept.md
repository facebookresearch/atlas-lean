# Balance value metaconcept and its extremal trees

Let $\mathcal{BT}^\ast_n$ be the set of rooted binary tree shapes with $n\ge 1$ leaves. For an inner vertex $v$ with children $v_1,v_2$ let $n_{v_i}$ be the number of leaves below $v_i$ and let the **balance value** be $b_T(v)=|n_{v_1}-n_{v_2}|$. The balance value sequence $\mathcal{B}(T)$ is the multiset of the $n-1$ balance values of $T$. For a function $f:\mathbb{R}\to\mathbb{R}$ the (first-order) **balance value metaconcept** is

$$\Phi^{\mathcal{B}}_f(T)=\sum_{v\ \text{inner}} f\big(b_T(v)\big).$$

Call a statistic a binary imbalance index if the caterpillar $T^{cat}_n$ (the tree with a single cherry) is its unique maximizer on $\mathcal{BT}^\ast_n$ for every $n$, and the fully balanced tree $T^{fb}_h$ (all $2^h$ leaves at depth $h$) is its unique minimizer whenever $n=2^h$. Let $T^{mb}_n$ be the maximally balanced tree, in which every inner vertex has $b_T(v)\le 1$, and let $c_n$ be the minimum Colless index on $\mathcal{BT}^\ast_n$.

1. If $f$ is increasing, $T^{cat}_n$ maximizes $\Phi^{\mathcal{B}}_f$ on $\mathcal{BT}^\ast_n$ and, for $n=2^h$, $T^{fb}_h$ minimizes it; both are unique when $f$ is strictly increasing. Hence $\Phi^{\mathcal{B}}_f$ is a binary imbalance index for every strictly increasing $f$.
2. If $f(b)=mb+a$ with $m>0$, then $\Phi^{\mathcal{B}}_f=m\,C(T)+(n-1)a$ with $C$ the Colless index, so its minimizers are exactly the Colless minimizers.
3. If $f$ is strictly increasing and convex, $T^{mb}_n$ minimizes $\Phi^{\mathcal{B}}_f$ on $\mathcal{BT}^\ast_n$ for all $n$, uniquely if in addition $f(1)-f(0)<f(2)-f(1)$.
4. For increasing $f$ the maximum value is $\sum_{i=0}^{n-2} f(i)$; for strictly increasing convex $f$ the minimum value is $c_n f(1)+(n-1-c_n)f(0)$.

## Expansion

Sorting the sequence turns the comparison into a majorization-free componentwise one: a tree minimizes $\sum_i f(Seq(T)_i)$ for every increasing $f$ iff its sorted sequence is componentwise smallest among all trees with $n$ leaves (Lemma 3.4). The caterpillar has sorted balance sequence $(0,1,\dots,n-2)$, and induction on attaching a cherry shows every other tree is componentwise below it. The fully balanced tree has all balance values $0$. In the convex case the Colless minimum $c_n$ is attained with $c_n$ balance values equal to $1$ and the rest $0$ by $T^{mb}_n$; convexity makes splitting any larger balance value into ones no worse, and local strict convexity at $0,1,2$ makes it strictly better. The quadratic Colless index ($f(b)=b^2$) and the Colless index ($f(b)=b$) are the classical instances.

## Sources

- Mareike Fischer, Tom Niklas Hamann, Kristina Wicke, "Metaconcepts of rooted tree balance", *Bulletin of Mathematical Biology* 87(9) (2025), 134, Theorem 3.6, Corollary 3.7, Theorem 3.8, Propositions 3.12 and 3.13, <https://doi.org/10.1007/s11538-025-01509-y> (preprint arXiv:2506.08614).
