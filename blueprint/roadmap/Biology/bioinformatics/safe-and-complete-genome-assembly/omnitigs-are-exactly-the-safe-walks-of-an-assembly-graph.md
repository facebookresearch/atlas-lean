# Omnitigs are exactly the safe walks of an assembly graph

**Setting.** Model genome assembly on a strongly connected directed graph $G=(V,E)$ (e.g. a de Bruijn or string graph) whose possible genome reconstructions are the *closed arc-covering walks*, i.e. circular walks traversing every arc at least once. A walk is *safe* if it is a subwalk of every closed arc-covering walk, so it appears in every possible solution. For an arc $e$ write $t(e)$ and $h(e)$ for its tail and head. A walk $W=e_0e_1\cdots e_\ell$ is an *omnitig* if for all $1\le i\le j\le\ell$ there is no nonempty *forbidden path* from $t(e_j)$ to $h(e_{i-1})$ whose first arc differs from $e_j$ and whose last arc differs from $e_{i-1}$.

**Theorem (Tomescu–Medvedev characterization).** If $G$ is strongly connected and not a single closed path, a walk is a subwalk of all closed arc-covering walks of $G$ iff it is an omnitig. Unitigs (paths whose internal nodes have in- and out-degree one) and their univocal extensions are omnitigs, but omnitigs can be much longer.

**Structural properties.** Call an arc a *join* arc if its head has in-degree at least two and a *split* arc if its tail has out-degree at least two.
1. For each split arc $g$ there is a unique left-maximal omnitig ending with $g$, and for each join arc $f$ a unique right-maximal omnitig starting with $f$.
2. *(Extension)* If $fW$ is an omnitig with $f$ a join arc, then $fWg$ is an omnitig iff $g$ is the only arc with $t(g)=h(W)$ from whose head there is a path to $h(f)$ in $G\setminus f$.
3. *(Y-lemma)* If $fWg$ is an omnitig with $f$ a join arc, $g$ a split arc and $W$ a join-free path, then $fWg'$ is not an omnitig for any sibling split arc $g'\ne g$ of $g$ (and symmetrically for sibling join arcs when $W$ is split-free).

## Expansion

A forbidden path lets a closed covering walk enter the middle of $W$ and leave it early, so its absence is exactly what forces every covering walk to traverse $W$ in full. The extension property turns the omnitig test into a single reachability query in $G$ minus one arc; with the Georgiadis et al. data structure for reachability under single arc failures (linear preprocessing, constant-time queries), omnitigs can be grown one arc at a time in constant time per step.

## Depends on

- [De Bruijn multigraph of a string](../de-bruijn-graph-genome-assembly/de-bruijn-edges.md)

## Sources

- Massimo Cairo, Romeo Rizzi, Alexandru I. Tomescu and Elia C. Zirondelli, "Genome assembly, from practice to theory: safe, complete and linear-time", arXiv:2002.10498 (2020), Sections 1–3 (definition of omnitigs, the characterization of safe walks restated from Tomescu and Medvedev, the extension property and the Y-lemma), <https://doi.org/10.48550/arXiv.2002.10498>.
