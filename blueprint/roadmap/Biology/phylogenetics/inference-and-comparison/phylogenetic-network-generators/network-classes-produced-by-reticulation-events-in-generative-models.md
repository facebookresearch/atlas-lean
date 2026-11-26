# Network classes produced by reticulation events in generative models

**Setting.** A rooted binary phylogenetic network is grown by a branching process acting on its current leaves. Besides *speciation* (a leaf becomes a cherry) and *extinction* (a leaf is removed), three local reticulation events act on a pair of current leaves $x,y$:

- **y-type (merging):** $x$ and $y$ are glued into one reticulation node with a single new leaf $z$ below it;
- **n-type (horizontal gene transfer or introgression):** new leaves $x'$ below $x$ and $y'$ below $y$ are added together with a horizontal arc from $x$ to $y$ (or $y$ to $x$);
- **m-type (hybrid speciation):** $x$ and $y$ both branch, and one new child of each is glued into a reticulation, giving three new leaves $x',y',z$.

A network is *tree-child* if every non-leaf node has a child that is not a reticulation; *temporal* if its nodes admit time labels that strictly increase along tree arcs and are equal across reticulation arcs; *orchard* if it can be reduced to a single vertex by a sequence of cherry and reticulated-cherry reductions.

**Theorem.**
1. Merging (y-type) together with speciation can generate every network topology.
2. HGT (n-type) together with speciation generates only orchard networks.
3. Hybridization (m-type) together with speciation generates only temporal tree-child networks, and every binary temporal tree-child network arises this way.
4. HGT (n-type) or hybridization (m-type), together with speciation and extinction, can generate every network.

Consequently the choice of reticulation mechanism in a birth–hybridization prior is not neutral: without extinction, HGT-driven and hybridization-driven generators are confined to orchard and temporal tree-child networks respectively, while merging-based generators (and any generator with extinction) reach all topologies.

## Expansion

For part 1, induct on the number of reticulations: if some leaf hangs directly below a reticulation, delete it and split the reticulation into two leaves to get a network with one fewer reticulation from which one merge restores the original; otherwise first prune a pendant subtree below a reticulation (speciation regrows it). Part 2 holds because speciation and n-type additions are exactly the inverse steps of cherry picking, so reversing the generation history is a cherry-picking sequence. In part 3, labelling each internal node by the step that created it is a temporal labelling, and an m-type event never creates adjacent reticulations or a tree node with two reticulation children; conversely a temporal labelling of a tree-child network can be refined so that each time slice is one speciation or one m-type event. Part 4 follows from part 1 since a merge equals an n-type event plus one extinction, or an m-type event plus two extinctions.

## Sources

- Remie Janssen, Pengyu Liu, "Comparing the topology of phylogenetic network generators", arXiv:2106.06727 (2021), Section 2 (reticulation types and network classes) and Lemmas B.1–B.4 of Appendix B, <https://doi.org/10.48550/arXiv.2106.06727>.
