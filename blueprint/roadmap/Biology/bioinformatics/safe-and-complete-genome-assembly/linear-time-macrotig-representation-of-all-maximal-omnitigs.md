# Linear-time macrotig representation of all maximal omnitigs

**Setting.** Let $G$ be a strongly connected directed graph with $n$ nodes and $m$ arcs, viewed as an assembly graph whose safe walks are its omnitigs. A *maximal omnitig* is an omnitig that is not a proper subwalk of another omnitig. The *univocal extension* $U(W)$ of a walk $W$ appends the longest path whose nodes, except the last, have out-degree one, and prepends the longest path whose nodes, except the first, have in-degree one.

**Theorem (macrotig representation).** There is an $O(m)$-size representation of all maximal omnitigs of $G$, consisting of a set $\mathcal M$ of walks (*maximal macrotigs*) of total length $O(n)$ and a set $\mathcal F$ of arcs, such that every maximal omnitig is the univocal extension of a subwalk of a walk in $\mathcal M$ or of an arc in $\mathcal F$. The sets $\mathcal M$, $\mathcal F$ and the endpoints of the macrotig subwalks whose univocal extensions are maximal omnitigs can be computed in $O(m)$ time.

**Corollaries.**
1. All maximal omnitigs can be enumerated in time linear in their total length (output-optimal).
2. The lengths of all maximal omnitigs can be computed in total time $O(m)$.
3. Maximal microtigs (the building blocks inside "macronodes") have total length $O(n)$ and are computable in $O(m)$ time; every arc that is not self-bivalent lies in at most one maximal macrotig.

Since omnitigs are exactly the safe walks, this gives a safe and complete genome-assembly algorithm (it reports everything that can be safely assembled) running in linear time, the same complexity as computing unitigs.

## Expansion

The graph is decomposed around *bivalent* nodes (both in- and out-degree at least two) into macronodes. Inside a macronode, the Y-lemma shows each join arc continues into at most one split arc in an omnitig, giving short microtigs; across macronodes these chain into macrotigs, which cannot branch, so their total length is linear. Every maximal omnitig is then a univocally extended subwalk of a macrotig, and the extension property with constant-time single-failure reachability queries finds the subwalk endpoints in linear time.

## Depends on

- [Omnitigs are exactly the safe walks of an assembly graph](omnitigs-are-exactly-the-safe-walks-of-an-assembly-graph.md)

## Sources

- Massimo Cairo, Romeo Rizzi, Alexandru I. Tomescu and Elia C. Zirondelli, "Genome assembly, from practice to theory: safe, complete and linear-time", arXiv:2002.10498 (2020), Section 1 (main theorem on the macrotig representation and the enumeration corollaries), Sections 4–6 and Appendix B (maximal microtigs and macrotigs), <https://doi.org/10.48550/arXiv.2002.10498>.
