# Linear-time macrotig representation of all maximal omnitigs

**Setting.** Let $G$ be a strongly connected directed graph with $n$ nodes and $m$ arcs that is not a single closed path, viewed as an assembly graph. [Omnitigs](../../omnitigs-and-safe-walks-in-genome-assembly/is-omnitig.md) of $G$ are exactly its nonempty [safe](../../omnitigs-and-safe-walks-in-genome-assembly/is-safe.md) walks: [omnitigs are safe](../../omnitigs-and-safe-walks-in-genome-assembly/is-safe-2.md), and, since a strongly connected graph has a circular arc-covering walk, [safe walks are omnitigs](../../omnitigs-and-safe-walks-in-genome-assembly/is-omnitig-of-is-safe.md). A *maximal omnitig* is an omnitig that is not a proper subwalk of another omnitig. The *univocal extension* $U(W)$ of a walk $W$ appends the longest path whose nodes, except the last, have out-degree one, and prepends the longest path whose nodes, except the first, have in-degree one.

**Theorem (macrotig representation).** There is an $O(m)$-size representation of all maximal omnitigs of $G$, consisting of a set $\mathcal M$ of walks (*maximal macrotigs*) of total length $O(n)$ and a set $\mathcal F$ of arcs, such that every maximal omnitig is the univocal extension of a subwalk of a walk in $\mathcal M$ or of an arc in $\mathcal F$. The sets $\mathcal M$, $\mathcal F$ and the endpoints of the macrotig subwalks whose univocal extensions are maximal omnitigs can be computed in $O(m)$ time.

**Corollaries.**
1. All maximal omnitigs can be enumerated in time linear in their total length (output-optimal).
2. The lengths of all maximal omnitigs can be computed in total time $O(m)$.
3. Maximal microtigs (the building blocks inside "macronodes") have total length $O(n)$ and are computable in $O(m)$ time; every arc that is not self-bivalent lies in at most one maximal macrotig.

Since omnitigs are exactly the safe walks, this gives a safe and complete genome-assembly algorithm (it reports everything that can be safely assembled) running in linear time, the same complexity as computing unitigs.

## Expansion

The graph is decomposed around *bivalent* nodes (both in- and out-degree at least two) into macronodes. Inside a macronode, the Y-intersection property shows each join arc continues into at most one split arc in an omnitig, giving short microtigs; across macronodes these chain into macrotigs, which cannot branch, so their total length is linear. Every maximal omnitig is then a univocally extended subwalk of a macrotig, and the extension property with constant-time single-failure reachability queries, applied after transforming $G$ to constant degree, finds the subwalk endpoints in linear time.

## Depends on

- [Omnitig](../../omnitigs-and-safe-walks-in-genome-assembly/is-omnitig.md)
- [Omnitigs are safe walks](../../omnitigs-and-safe-walks-in-genome-assembly/is-safe-2.md)
- [Safe walks are omnitigs](../../omnitigs-and-safe-walks-in-genome-assembly/is-omnitig-of-is-safe.md)
- [Safe walk in a multigraph](../../omnitigs-and-safe-walks-in-genome-assembly/is-safe.md)

## Proof depends on

- [Extension property of omnitigs](extension-property-of-omnitigs.md)
- [Y-intersection property of omnitigs](y-intersection-property-of-omnitigs.md)

## Sources

- Massimo Cairo, Romeo Rizzi, Alexandru I. Tomescu and Elia C. Zirondelli, "Genome assembly, from practice to theory: safe, complete and linear-time", arXiv:2002.10498 (2020); published in ICALP 2021, LIPIcs 198, paper 43, <https://doi.org/10.4230/LIPIcs.ICALP.2021.43>; numbering as in the arXiv version: Section 1 (Theorem 2 and Corollaries 3–4 on the macrotig representation and enumeration), Sections 4–6 and Appendix B (maximal microtigs and macrotigs).
