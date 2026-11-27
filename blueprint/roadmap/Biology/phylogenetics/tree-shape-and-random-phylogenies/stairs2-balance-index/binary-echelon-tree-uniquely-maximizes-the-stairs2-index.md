# The binary echelon tree uniquely maximizes the stairs2 index

**Binary echelon tree.** For $n\ge2$ let $k$ be the unique power of two with $n/2\le k<n$. The binary echelon tree $BE_n$ is defined recursively by $BE_0=\emptyset$, $BE_1=$ a single vertex, and

$$BE_n=\big(T^{fb}_{\log_2 k},\,BE_{n-k}\big),$$

a fully balanced tree on $k$ leaves joined at the root with a binary echelon tree on $n-k$ leaves. When $n=2^h$ this is the fully balanced tree $T^{fb}_h$.

**Theorem.** For every $n\ge1$ there is exactly one rooted binary tree with $n$ leaves of maximum stairs2 index, namely $BE_n$.

**Corollary (recursion for the maximum).** Let $\mathrm{st}_2(n)$ denote the maximum stairs2 index on $n$ leaves. Then $\mathrm{st}_2(0)=\mathrm{st}_2(1)=0$ and, for $n\ge2$ with $k=2^{\lfloor\log_2 n\rfloor}$,

$$\mathrm{st}_2(n)=\frac{1}{n-1}\Big((k-1)+(n-k-1)\,\mathrm{st}_2(n-k)+\frac{n-k}{k}\Big).$$

**Corollary (closed form).** If $n\ge2$ has binary expansion $n=\sum_{i=1}^{\ell}2^{a_i}$ with $0\le a_1<a_2<\dots<a_\ell$, then

$$\mathrm{st}_2(n)=\frac{1}{n-1}\left(\sum_{i=1}^{\ell}\big(2^{a_i}-1\big)+\sum_{i=1}^{\ell-1}\frac{\sum_{j=1}^{i}2^{a_j}}{2^{a_{i+1}}}\right).$$

For example $\mathrm{st}_2(3)=\tfrac12\big(0+1+\tfrac12\big)=\tfrac34$ and $\mathrm{st}_2(2^h)=1$.

## Proof sketch

If $T=(T_1,T_2)$ is maximal, then both $T_1$ and $T_2$ are maximal for their own leaf numbers: replacing $T_1$ by a tree with larger index increases $\mathrm{st}_2(T)$ through the root recursion, since $n_1,n_2$ and the root ratio are unchanged. Induction on $n$ then reduces the problem to choosing the root split $(n_1,n_2)$ and comparing $\frac{(n_1-1)\mathrm{st}_2(n_1)+(n_2-1)\mathrm{st}_2(n_2)+n_2/n_1}{n-1}$ across splits; a case analysis by exchange arguments (moving leaves between the two sides and comparing the resulting trees) shows that the unique optimum takes $n_1=k$ to be a power of two (so the larger side is fully balanced with index $1$) and recurses on $n-k$. Unrolling the recursion along the binary expansion of $n$ gives the closed form: each power-of-two block contributes $2^{a_i}-1$ inner vertices of ratio $1$, and the spine vertex joining block $a_{i+1}$ to the echelon tree on the smaller blocks contributes $\sum_{j\le i}2^{a_j}/2^{a_{i+1}}$.

## Depends on

- [Stairs2 index and its root recursion](stairs2-index-and-its-root-recursion.md)

## Sources

- Bryan Currie and Kristina Wicke, "On the maximum value of the stairs2 index", *Advances in Applied Mathematics* 159 (2024), 102732, <https://doi.org/10.1016/j.aam.2024.102732>. Preprint version: arXiv:2401.08838 (2024), Section 2 (binary echelon tree), Section 4.1 (Theorem 1, Lemma 2) and Section 4.2 (Corollaries 1 and 2), <https://doi.org/10.48550/arXiv.2401.08838>.
