# Locally good neural codes

A neural code is locally good when it contains every mandatory codeword of its simplicial complex, the faces whose links are not contractible; equivalently, no realization of it by open sets has a local obstruction.

Let $\mathcal{C}$ be a [neural code](neural-codes-and-their-realizations.md) on $n$ neurons. Its *simplicial complex* $\Delta(\mathcal{C})$ is the smallest [simplicial complex](../rational-homology-of-simplicial-complexes/is-simplicial-complex.md) on $[n]$ containing $\mathcal{C}$; its facets are the maximal codewords. For a face $\sigma$ of a simplicial complex $\Delta$, the [*link*](../rational-homology-of-simplicial-complexes/link.md) is $\mathrm{Lk}_\sigma(\Delta) = \{\tau \in \Delta : \sigma \cap \tau = \emptyset,\ \sigma \cup \tau \in \Delta\}$. A nonempty face $\sigma$ of $\Delta$ is a *mandatory codeword* of $\Delta$ if $\mathrm{Lk}_\sigma(\Delta)$ is not [contractible](../../../Topology/algebraic-topology/contractibility-and-local-contractibility/contractible-space.md), that is, its geometric realization is not a contractible space. The code $\mathcal{C}$ is *locally good* if it contains every mandatory codeword of $\Delta(\mathcal{C})$. The empty face is excluded: the source handles codes without the empty codeword through $\mathcal{C} \cup \{\emptyset\}$ (Remark 2.5 and the proof of Theorem 3.13), so $\mathcal{C}$ is locally good exactly when $\mathcal{C} \cup \{\emptyset\}$ is locally good in the printed sense. Counting $\emptyset$ would make the code $\{\{1\}, \{2\}\}$, realized by two disjoint intervals covering the stimulus space, fail to be locally good although it is a good-cover code.

The source defines local goodness as the absence of local obstructions: for a realization $\mathcal{U}$ of $\mathcal{C}$ by open sets, a *local obstruction* is a pair $(\sigma, \tau)$ with $\sigma \neq \emptyset$, $\tau \neq \emptyset$, $\bigcap_{i \in \sigma} U_i \subseteq \bigcup_{i \in \tau} U_i$ and $\mathrm{Lk}_\sigma(\Delta(\mathcal{C})|_{\sigma \cup \tau})$ not contractible, and this does not depend on the realization (Definition 2.14). By Proposition 2.18 (Curto et al.) this is equivalent to the definition above, and every mandatory codeword is an intersection of maximal codewords. The link of a facet is $\{\emptyset\}$, whose geometric realization is empty and so not contractible; every facet is therefore mandatory, and it is a codeword.

Good-cover codes are locally good (Proposition 2.15), and Chen, Frick and Shiu proved the converse (Theorem 3.13).

## Depends on

- [Neural codes and their realizations](neural-codes-and-their-realizations.md)
- [Finite abstract simplicial complex](../rational-homology-of-simplicial-complexes/is-simplicial-complex.md)
- [Link](../rational-homology-of-simplicial-complexes/link.md)
- [Contractible space](../../../Topology/algebraic-topology/contractibility-and-local-contractibility/contractible-space.md)

## Proof depends on

None.

## Sources

- Aaron Chen, Florian Frick and Anne Shiu, *Neural codes, decidability, and a new local obstruction to convexity*, SIAM Journal on Applied Algebra and Geometry 3 (2019), no. 1, 44–66, https://doi.org/10.1137/18M1186563; read as arXiv:1803.11516v2: Definitions 2.6, 2.7, 2.9, 2.14 and 2.17, Remark 2.5, Propositions 2.15 and 2.18, and Theorem 3.13 with its proof.
