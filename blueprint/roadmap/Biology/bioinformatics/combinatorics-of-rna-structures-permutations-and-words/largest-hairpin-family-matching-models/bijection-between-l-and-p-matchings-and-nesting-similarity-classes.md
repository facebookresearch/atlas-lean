# Bijection between L & P matchings and nesting-similarity classes of matchings

**Nesting-similarity.** Two complete matchings $M,N\in\mathcal M(n)$ are *nesting-similar*, $M\sim_{ne}N$, if they have the same LR-sequence and the same number of nested pairs, $ne(M)=ne(N)$. For a fixed LR-sequence the noncrossing matching has the maximum number of nestings, and every value $0\le i\le ne(nc(M))$ is attained, so the classes are indexed by pairs (Dyck path, nesting count). Their number equals $|\mathcal{LP}_n| = 2\cdot 4^{n-1}-\frac{3n-1}{2n+2}\binom{2n}{n}$.

**Intermediate set.** $\mathcal{NCN}_n$ is the set of triples $(M,a,b)$ with $M$ a noncrossing matching on $n$ edges and either $a=b=0$ or $a<b$ a nested pair of edges of $M$.

**Theorem.**

1. The map $\phi:\mathcal{LP}_n\to\mathcal{NCN}_n$, with $\phi(M)=(M,0,0)$ for noncrossing $M$ and $\phi(M)=(nc(M),\max A,\max B)$ when $M$ contains the inflated hairpin $(A,B)$, is a bijection.
2. List the nested pairs of a noncrossing $M$ as $nep(M)=\{(a_1,b_1),\ldots,(a_k,b_k)\}$, ordered lexicographically with priority on the second coordinate, and set $M_0=M$, $M_i=(a_i,b_i).M_{i-1}$, where $(a,b).M$ swaps the left endpoints of edges $a$ and $b$. Then $M_i$ has the LR-sequence of $M$ and exactly $k-i$ nested pairs, and $\tau(M,a_i,b_i)=M_i$, $\tau(M,0,0)=M$ is a bijection from $\mathcal{NCN}_n$ onto a set $\mathcal{NS}_n$ of representatives of the nesting-similarity classes.
3. Hence $\sigma=\tau\circ\phi:\mathcal{LP}_n\to\mathcal{NS}_n$ is a bijection between L & P matchings and nesting-similarity classes. It fixes every noncrossing matching, and $M$ and $\sigma(M)$ have the same LR-sequence.

## Depends on

- [L & P matchings as models of pseudoknotted RNA secondary structures](l-and-p-matchings-and-inflated-hairpins.md)

## Expansion

In a noncrossing matching, $a<b$ are nested exactly when $b$'s right endpoint precedes $a$'s. Processing nested pairs in the stated order, the next pair $(a_{i+1},b_{i+1})$ is always adjacent in the left-endpoint order of $M_i$, so each swap destroys exactly one nesting and creates no other change in the nesting count, giving $ne(M_i)=k-i$. Thus choosing a nested pair in a noncrossing matching is the same as choosing a nesting-similarity class with that LR-sequence and fewer than the maximum nestings. On the other side, an L & P matching with crossings is determined by its Dyck path and the two maximal hairpin edges. Composing the two encodings explains the equality of the two counts, first observed numerically, by an explicit structure-preserving map.

## Sources

- Megan A. Martinez, Manda Riehl, "A bijection between the set of nesting-similarity classes and L & P matchings", Discrete Mathematics & Theoretical Computer Science 19(2) (2018), <https://doi.org/10.23638/dmtcs-19-2-1>. Published version of arXiv:1704.07902, cited next; locators there refer to the arXiv version.
- Megan A. Martinez and Manda Riehl, "A bijection between the set of nesting-similarity classes and L & P matchings", arXiv:1704.07902 (2017), Section 1 (definitions and enumeration), Section 2 (Definition 1, Lemma 1, Theorem 1), Section 3 (Lemmas 2-4, Theorems 2 and 3, Corollary 1), <https://doi.org/10.48550/arXiv.1704.07902>.
