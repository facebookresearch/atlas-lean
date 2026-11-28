# Extremal values of the symmetry nodes index

Let $T$ be a rooted binary tree with $n$ leaves. An interior node is a **symmetry node** if its two maximal pendant subtrees are isomorphic (same shape). With $s(T)$ the number of symmetry nodes, the **symmetry nodes index** is

$$\mathrm{SNI}(T)=(n-1)-s(T),$$

the number of interior nodes that are not symmetry nodes; small values mean balanced trees. It satisfies $\mathrm{SNI}((T_a,T_b))=\mathrm{SNI}(T_a)+\mathrm{SNI}(T_b)+\delta$, with $\delta=0$ if the root is a symmetry node and $\delta=1$ otherwise.

Let $wt(n)$ be the binary weight of $n$ (number of ones in its binary expansion). A **rooted binary weight tree** for $n=\sum_i n_i2^i$ is any tree obtained from an arbitrary rooted binary "top tree" with $wt(n)$ leaves by replacing its leaves with fully balanced trees of heights $i$, one for each $i$ with $n_i=1$.

**Theorems.**
1. $\mathrm{SNI}(T)$ can be computed in $O(n)$ time and $O(n)$ space.
2. For $n\ge2$, $\max_T\mathrm{SNI}(T)=n-2$, attained uniquely by the caterpillar.
3. $\min_T\mathrm{SNI}(T)=wt(n)-1$, attained exactly by the rooted binary weight trees.
4. The number of $\mathrm{SNI}$-minimal trees with $n$ leaves is $(2\,wt(n)-3)!!$ (equal to $1$ when $wt(n)=1$).

In particular the fully balanced tree is the unique minimizer, with $\mathrm{SNI}=0$, exactly when $n$ is a power of two.

## Expansion

The root of a tree is a symmetry node only if both pendant subtrees have the same number of leaves and the same shape; inductively, a tree with $\mathrm{SNI}=0$ must be fully balanced, so $n$ is a power of two. For general $n$, induction on $n$ using the recursion for $\mathrm{SNI}$ and the subadditivity $wt(a+b)\le wt(a)+wt(b)$ yields $\mathrm{SNI}\ge wt(n)-1$, with equality exactly when every non-symmetry node lies in a top tree over fully balanced blocks. The count $(2k-3)!!$ is the number of rooted binary top trees on $k=wt(n)$ distinguishable blocks. Linear time follows from a Colbourn–Booth-style bottom-up labelling that assigns equal labels exactly to isomorphic subtrees at the same depth, so a node is a symmetry node iff its two children have equal labels.

## Sources

- S. J. Kersting, M. Fischer, "Measuring tree balance using symmetry nodes -- a new balance index and its extremal properties", arXiv:2105.00719 (2021), Section 2 (definitions of symmetry node, SNI, binary weight), Definition 3.4 (weight trees), Lemma 3.2 (recursion), Theorems 3.1, 3.3, 3.5, 3.9, Proposition 3.6 and Lemma 3.8 (subadditivity of $wt$), <https://doi.org/10.48550/arXiv.2105.00719>.
