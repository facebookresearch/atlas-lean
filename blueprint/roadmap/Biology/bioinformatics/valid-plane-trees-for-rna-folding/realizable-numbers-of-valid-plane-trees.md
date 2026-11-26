# Realizable numbers of valid plane trees for RNA primary sequences

**Setting.** A *complementary alphabet of size $m$* consists of $m$ pairs of complementary letters $\{A,\bar A,B,\bar B,\ldots\}$ (for RNA, the Watson-Crick pairs $A$-$U$ and $C$-$G$). Given a rooted plane tree $T$ with $n$ edges and a word $P=p_1\cdots p_{2n}$, label the edges of $T$ by walking counter-clockwise around $T$ from the root, so each edge receives two letters; $T$ is *$P$-valid* if every edge receives a complementary pair. Equivalently, writing $P$ around a circle, a $P$-valid tree is a noncrossing perfect matching of the $2n$ positions in which every matched pair is complementary. Let $V(P)$ be the set of $P$-valid plane trees, $\mathcal P(n,m)$ the set of words of length $2n$ over an alphabet of size $m$ with $V(P)\neq\emptyset$, and

$$R(n,m) = \{\,k\ge 1 : |V(P)|=k \text{ for some } P\in\mathcal P(n,m)\,\}.$$

**Theorem (every count is realized with one letter pair).** For every $k\in\mathbb N^+$ there is $n$ with $k\in R(n,1)$. Explicitly, for $P_{k,\ell}=A^k\bar A^k A^\ell\bar A^\ell$,

$$|V(P_{k,\ell})| = \begin{cases} |V(P_{k-1,\ell})| & k>\ell,\\ |V(P_{k,\ell-1})| & \ell>k,\\ 1+|V(P_{k,\ell-1})| & k=\ell,\end{cases}$$

so $|V(P_{k,k})|=k+1$ and $k+1\in R(2k,1)$.

**Monotonicity.** $R(n,m)\subseteq R(n+1,m)$ for all $n,m\ge 1$.

**Alphabet dependence.** The conjecture that $R(n,m)=R(n,1)$ for all $m$ is false: over $\{A,\bar A,B,\bar B\}$ the word $P=B\bar B\bar AAA\bar A\bar AAB\bar BA\bar AA\bar A$ (with $n=7$) has $|V(P)|=11$, whereas $11\notin R(7,1)$ by the enumeration of the original conjecture paper.

## Depends on

- [RNA secondary structure](../nussinov-algorithm-for-rna-secondary-structure/is-structure.md)

## Expansion

*Recurrence.* In $P_{k,\ell}$ with $k>\ell$, position $p_k$ (the last $A$ of the first block) must pair with $p_{k+1}$: a partner to its left is not complementary, and a partner further right would enclose unequal numbers of $A$ and $\bar A$, impossible in a noncrossing matching. Deleting this adjacent pair reduces $k$ by one. When $k=\ell$, $p_k$ pairs either with $p_{k+1}$ or with $p_{3k+1}$, and in the latter case both sides have a unique matching, contributing the extra $1$.

*Monotonicity.* Given $P$ with $|V(P)|=k$, insert an adjacent pair $\bar AA$ at a position chosen so that the two new letters must be matched to each other in every valid noncrossing matching; then $|V(P')|=k$. The position comes from the classical gas-station lemma (if stations around a circular track hold exactly the fuel for one lap, some starting station lets a car finish the lap): put one station per occurrence of $A$, spaced by the number of $\bar A$'s between consecutive $A$'s.

*Counterexample.* Matching the adjacent $B\bar B$ pairs leaves 7 valid matchings of the $A$-letters, and matching the distant pairs leaves $2\cdot 2=4$, for $11$ in total.

## Sources

- Adam Zsolt Wagner, "A note on some conjectures about combinatorial models for RNA secondary structures", arXiv:1901.10238 (2019), Section 1 (definitions, Conjectures 1.1-1.2, Theorem 1.3) and Section 2 (counterexample, Lemma 2.1, Theorem 2.2, Proposition 2.3), <https://doi.org/10.48550/arXiv.1901.10238>.
