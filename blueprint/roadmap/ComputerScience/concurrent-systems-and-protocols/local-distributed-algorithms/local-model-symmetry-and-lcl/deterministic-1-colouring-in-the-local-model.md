# Deterministic (Δ + 1)-colouring in the LOCAL model

On finite graphs of maximum degree at most $\Delta \ge 1$ with an initial proper colouring by colours below $C$ (for instance distinct identifiers), where every node knows $\Delta$ and $C$, a deterministic LOCAL algorithm computes a proper $(\Delta + 1)$-colouring within $O(\Delta^2 + \log^* C)$ rounds: Linial's colour reduction with cover-free set families, iterated and followed by one final cover-free reduction step, reaches $O(\Delta^2)$ colours in $O(\log^* C)$ rounds (Hirvonen and Suomela, Section 4.8), and then each greedy round, in which every vertex whose colour is a local maximum recolours to the smallest free colour, reduces the number of colours from $x$ to $\max(x - 1, \Delta + 1)$ (Lemma 4.1). If the nodes know $\Delta$, the number $n$ of nodes and a polynomial bound $n^c$ on the identifiers, inserting additive-group colour reduction between the two phases gives $(\Delta + 1)$-colourings from identifiers in $O(\Delta + \log^* n)$ rounds (Hirvonen and Suomela, Theorem 4.8).

## Proof sketch

A $\Delta$-cover-free family of $x$ subsets of a small base set lets every node pick an element of its own colour's set that lies in none of its neighbours' sets, which reduces $x$ colours to $O(\Delta^2 \log^2 x)$ in one round; iterating reaches at most $36(\Delta + 1)^2\bigl(\log 36 + 2\log(\Delta + 1)\bigr)^2$ colours after at most $\log^* C$ rounds, and a polynomial-based cover-free family gives $O(\Delta^2)$ colours in one more round. Then eliminate one colour class above $\Delta + 1$ per round: local maxima form an independent set and each finds a free colour among $\Delta + 1$.

## Depends on

- [The LOCAL model](../../distributed-execution-models/the-local-model.md)

## Sources

- Nathan Linial, "Locality in Distributed Graph Algorithms", SIAM Journal on Computing 21(1), 1992.
- Juho Hirvonen and Jukka Suomela, "Distributed Algorithms 2020", Online textbook, Aalto University, 2020, Lemma 4.1, Section 4.8 and Theorem 4.8.
