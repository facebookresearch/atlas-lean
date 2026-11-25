# Discrete Loomis–Whitney inequality (three dimensions)

For every finite set $V$ of triples $(x, y, z)$,

$$|V|^2 \le |V_{yz}| \cdot |V_{xz}| \cdot |V_{xy}|,$$

where $V_{yz}$, $V_{xz}$ and $V_{xy}$ are the images of $V$ under the three projections onto pairs of coordinates. The coordinates may come from any three sets; no lattice structure is used. Equality holds for every box $X \times Y \times Z$.

This is the three-dimensional case of L. H. Loomis and H. Whitney, *An inequality related to the isoperimetric inequality*, Bull. Amer. Math. Soc. 55 (1949), 961–962, as stated for lattice points in Lemma 1 of G. Ballard, J. Demmel, O. Holtz and O. Schwartz, *Minimizing communication in numerical linear algebra*, arXiv:0905.2485, and in Theorem 2.1 of M. Christ, J. Demmel, N. Knight, T. Scanlon and K. Yelick, *Communication lower bounds and optimal algorithms for programs that reference arrays, Part 1*, arXiv:1308.0068.

**Proof.** Slice $V$ by the last coordinate. The slice $S_z$ at height $z$ injects into $V_{xy}$, so $|S_z| \le |V_{xy}|$; it also injects into $A_z \times B_z$, where $A_z$ and $B_z$ are the points of $V_{xz}$ and $V_{yz}$ at height $z$, so $|S_z| \le a_z b_z$. Hence $|S_z|^2 \le (|V_{xy}|\, a_z)\, b_z$, and the Cauchy–Schwarz inequality gives $|V|^2 = (\sum_z |S_z|)^2 \le (\sum_z |V_{xy}|\, a_z)(\sum_z b_z) = |V_{xy}|\,|V_{xz}|\,|V_{yz}|$.

## Background

- [Shearer's entropy inequality](../../../InformationTheory/information-inequalities/shearer-s-entropy-inequality/shearer-entropy-inequality.md): the entropy form of projection inequalities; applied to the uniform distribution on $V$ and the cover of the three coordinates by the three pairs, each coordinate covered twice, it gives this inequality.
