# Regular-tree equivalence of protocols as bisimilarity

Two protocols $S$ and $T$ are tree-equivalent, $S \simeq T$, when they are (strongly) bisimilar in
the protocol-tree transition system: there is a relation $\mathcal{R}$ containing $(S,T)$ such that
whenever $(S',T') \in \mathcal{R}$ and $S' \xrightarrow{\ell} S''$ there is $T''$ with $T'
\xrightarrow{\ell} T''$ and $(S'',T'') \in \mathcal{R}$, and symmetrically. The edges of a protocol
are determined by its head, so $\simeq$ compares the infinite trees denoted by protocols, not their
presentations by graphs and cursors.
