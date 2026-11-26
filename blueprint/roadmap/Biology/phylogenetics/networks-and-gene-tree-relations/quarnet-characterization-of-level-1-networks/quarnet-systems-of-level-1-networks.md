# Quarnet systems of level-1 networks

**Definitions.** Let $X$ be a finite set with $|X| \ge 4$ and $N$ a binary level-1 phylogenetic network on $X$ (an unrooted network in which no two cycles share a vertex). For $A \subseteq X$, $N|_A$ is obtained by deleting all edges not on a path between two elements of $A$, removing isolated vertices, and repeatedly suppressing degree-2 vertices and parallel edges. A **quarnet** (qnet) is a binary level-1 network on four leaves; there are four types: $a \ominus b \,|\, c \ominus d$ (a quartet tree), $a \oplus b \,|\, c \ominus d$ (one cycle and a non-trivial cut-edge), $a \oplus b \,|\, c \oplus d$ (two cycles), and $a \oplus b \oplus c \oplus d$ (a single 4-cycle with leaves in this cyclic order). A qnet system $\mathcal{F}$ on $X$ is

- **minimally dense** if every 4-subset of $X$ is the leaf set of exactly one qnet in $\mathcal{F}$;
- **consistent** if any two qnets of $\mathcal{F}$ induce isomorphic networks on every common 3-subset;
- **cyclative** if $a \oplus b \oplus c \oplus d,\ x \oplus a \oplus c \oplus d \in \mathcal{F}$ imply $a \oplus b \oplus d \oplus x \in \mathcal{F}$;
- **saturated** if, for all distinct $a, b, c, d, x$, each qnet of the form $a \star b \,|\, c \star d$ (with $\star \in \{\ominus, \oplus\}$) in $\mathcal{F}$ forces one of four qnets on $\{a, b, c, x\}$ or $\{a, x, c, d\}$ listed in the paper (the qnet analogue of quartet saturation: $ab|cd$ forces $ab|cx$ or $ax|cd$).

Write $\mathcal{F}(N) = \{N|_A : A \subseteq X, |A| = 4\}$.

**Theorem 2.** A minimally dense qnet system $\mathcal{F}$ on $X$ equals $\mathcal{F}(N)$ for some binary level-1 network $N$ on $X$, which is then unique, if and only if $\mathcal{F}$ is consistent, cyclative and saturated.

**Theorem 4.** Let $\mathcal{F}$ be minimally dense and consistent with $|X| \ge 5$, and let $\mathrm{cl}_2(\mathcal{F})$ be its closure under the paper's three two-qnet inference rules (CL1)–(CL3) (each rule is sound: every binary level-1 network displaying the two premises displays the conclusion). The following are equivalent:

1. $\mathcal{F} = \mathcal{F}(N)$ for a (necessarily unique) binary level-1 network $N$;
2. $\mathrm{cl}_2(\mathcal{F}) = \mathcal{F}$;
3. every 3-element subset of $\mathcal{F}$ is displayed by some binary level-1 network on $X$.

Moreover (Proposition 1), a binary level-1 network displays $\mathcal{F}$ iff it displays $\mathrm{cl}_2(\mathcal{F})$.

## Expansion

The model result is the Colonius–Schulze theorem (Theorem 1): a quartet system is the quartet set $\mathcal{Q}(T)$ of a unique phylogenetic tree iff it is thin (one quartet per support) and saturated. For Theorem 2, the quartets exhibited by cut-edges of the qnets in $\mathcal{F}$ form a thin saturated system (Lemma 2), so they come from a unique tree $T$; each high-degree vertex of $T$ is then replaced by a cycle, and cyclativity makes the cyclic orders read off the 4-cycle qnets glue into a single cyclic order around each such vertex. Theorem 4 says that level-1 networks, like trees, are certified by local checks: closure under the rules adds nothing exactly when the system is already realized, and realizability of all triples of qnets suffices.

## Sources

- K. T. Huber, V. Moulton, C. Semple, T. Wu, "Quarnet inference rules for level-1 networks", Bulletin of Mathematical Biology (2018), Theorems 1, 2 and 4, Lemma 2, Proposition 1, <https://doi.org/10.1007/s11538-018-0450-2> (PMC6061523).
