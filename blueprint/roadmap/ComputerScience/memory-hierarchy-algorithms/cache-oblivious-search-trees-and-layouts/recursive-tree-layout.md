# Prokop's recursive layout of a complete binary tree

The *van Emde Boas layout* of a complete binary tree of height $h$ stores it in a contiguous array as follows: cut the tree at depth $\lfloor h/2 \rfloor$ into a *top tree* consisting of the top $\lfloor h/2 \rfloor$ levels and the *bottom trees* below it; lay out the top tree recursively, followed by the bottom trees laid out recursively in left-to-right order. A tree of height $1$ is a single node, laid out trivially. Prokop states the cut as giving at most $2^{\lfloor h/2 \rfloor}$ bottom subtrees of height at most $\lceil h/2 \rceil$; for a complete binary tree of height $h$ (height counting levels) both hold with equality: there are exactly $2^{\lfloor h/2 \rfloor}$ bottom trees, each of height $h - \lfloor h/2 \rfloor = \lceil h/2 \rceil$.

## Depends on

- [The ideal-cache model](../cache-oblivious-algorithms/the-ideal-cache-model.md)

## Sources

- Harald Prokop, "Cache-Oblivious Algorithms", S.M. thesis, Massachusetts Institute of Technology (1999), MIT DSpace copy, Section 10.2 (the cache-oblivious layout $L(T) = L(T_0) \Vert L(T_1) \Vert \cdots \Vert L(T_k)$).
- Michael A. Bender, Erik D. Demaine, Martín Farach-Colton, "Cache-Oblivious B-Trees", SIAM Journal on Computing 35(2) (2005); FOCS (2000).
