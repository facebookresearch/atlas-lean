# Level-3 networks are reconstructible from their quarnets

**Setting.** Phylogenetic networks on $X$, blobs, level and decomposability are as in the companion article. For $x\in X$ let $N^{\mathcal P}_x$ be obtained from $N$ by deleting $x$ and its incident edge and then repeatedly (i) suppressing degree-$2$ vertices, (ii) replacing a pair of parallel edges by one edge and (iii) collapsing a blob with exactly two incident cut-edges to a vertex; for $|X|\ge 3$ the result is again a phylogenetic network on $X\setminus\{x\}$. A *quarnet* is a phylogenetic network with exactly four leaves. The quarnet set of $N$ is defined recursively by

$$ Q(N)=\{N\} \text{ if } |X|=4, \qquad Q(N)=\bigcup_{x\in X} Q(N^{\mathcal P}_x) \text{ if } |X|\ge 5 , $$

with isomorphic networks identified. $N$ is *reconstructible from its quarnets* if every phylogenetic network $N'$ with $Q(N')\cong Q(N)$ is isomorphic to $N$.

**Theorem.** Let $\mathcal N$ be a class of phylogenetic networks with at least five leaves such that, for each member with at least six leaves, every $N^{\mathcal P}_x$ is again (isomorphic to) a member of $\mathcal N$. Then every member of $\mathcal N$ is determined by its family $\{N^{\mathcal P}_x\}$ if and only if every member is reconstructible from its quarnets. The class of level-$3$ networks with at least five leaves and the class of decomposable networks with at least five leaves both have the first property. Consequently every level-$3$ phylogenetic network is reconstructible from its quarnets.

## Depends on

- [Leaf-reconstructibility of trees, decomposable and low-level networks](leaf-reconstructibility-of-trees-decomposable-and-low-level-networks.md)

## Expansion

The equivalence is an induction on $|X|$: for five leaves the family $\{N^{\mathcal P}_x\}$ is exactly the quarnet set, and for more leaves each $N^{\mathcal P}_x$ is, by induction, determined by its own quarnets, which are quarnets of $N$. The cleaning steps (ii)–(iii) make $N^{\mathcal P}_x$ differ from the plain leaf-deleted network $N_x$, so the leaf-reconstruction results are transferred by showing that for suitable leaves the two coincide and that a small set of such leaves already forces reconstruction. Since the level does not increase under leaf deletion and cleaning, the class of level-$3$ networks is closed as required.

## Sources

- L. van Iersel and V. Moulton, *Leaf-reconstructibility of phylogenetic networks*, arXiv:1701.08982 (2017). <https://doi.org/10.48550/arXiv.1701.08982> Definition 5, Proposition 2, Theorems 5–7 and Corollary 8 (Section 8). Published version: SIAM Journal on Discrete Mathematics 32 (2018) 2047–2066, <https://doi.org/10.1137/17m1111930>.
