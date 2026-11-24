# The digraph of a phylogenetic network is acyclic

For every [phylogenetic network](phylo-network.md) $N$, the [digraph](g.md) $D_N$ of the
network, with an edge $u \to v$ exactly when $u \in \mathrm{pa}(v)$, is acyclic: no node reaches
itself by a directed walk of positive length. This follows from the well-foundedness of the parent
relation.
