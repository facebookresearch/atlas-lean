# Prokop's recursive layout of a complete binary tree

The *van Emde Boas layout* of a complete binary tree of height $h$ stores it in a contiguous array as follows: cut the tree at depth $\lfloor h/2 \rfloor$ into a *top tree* of height $\lfloor h/2 \rfloor$ and $2^{\lfloor h/2 \rfloor}$ *bottom trees* of height $\lceil h/2 \rceil$; lay out the top tree recursively, followed by the bottom trees laid out recursively in left-to-right order. A tree of height $1$ is a single node.

## Depends on

- [The ideal-cache model](../cache-oblivious-algorithms/the-ideal-cache-model.md)

## Sources

- Harald Prokop, "Cache-Oblivious Algorithms", Master's thesis, Massachusetts Institute of Technology (1999).
- Michael A. Bender, Erik D. Demaine, Martín Farach-Colton, "Cache-Oblivious B-Trees", SIAM Journal on Computing 35(2) (2005); FOCS (2000).
