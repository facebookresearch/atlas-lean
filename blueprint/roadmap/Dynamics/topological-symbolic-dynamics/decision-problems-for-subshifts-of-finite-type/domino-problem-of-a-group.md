# Domino problem of a finitely generated group

The domino problem of a finitely generated group $G$ is the set of SFT presentations on $G$ whose subshift of finite type is empty; $G$ has decidable domino problem when this set is decidable.

Let SFT presentations $(A, \mathcal{F})$ and the subshifts $X_{(A,\mathcal{F})}$ they determine be as in [subshifts of finite type on a finitely generated group](subshifts-of-finite-type-on-groups.md). The *domino problem* of $G$ is the set

$$
\mathrm{DP}(G) = \{ (A, \mathcal{F}) : X_{(A,\mathcal{F})} = \emptyset \}
$$

of SFT presentations of the empty subshift. It is *decidable* when some algorithm decides, given an SFT presentation, whether it lies in $\mathrm{DP}(G)$.

## Depends on

- [Subshifts of finite type on a finitely generated group](subshifts-of-finite-type-on-groups.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

For $G = \mathbb{Z}$ the domino problem is decidable: a nonempty one-dimensional SFT is equivalent to a bi-infinite path, hence a cycle, in a finite graph. For $G = \mathbb{Z}^d$ with $d \ge 2$ it is undecidable (Berger), which is the tiling problem for Wang tiles: the valid tilings of a Wang tile set form a two-dimensional SFT, and every two-dimensional SFT is conjugate to a recoding of one.

## Sources

- N. Carrasco-Vargas, "On a Rice theorem for dynamical properties of SFTs on groups", Archiv der Mathematik 124 (2025), no. 6, 591–603, https://doi.org/10.1007/s00013-025-02125-x; read in arXiv:2401.10347v3 (Section 2 of arXiv:2401.10347v3, the domino problem).
- S. J. Esnay and M. Sablik, "Parametrization by horizontal constraints in the study of algorithmic properties of $\mathbb{Z}^2$-subshifts of finite type", Discrete and Continuous Dynamical Systems 43 (2023), no. 5, 2002–2046, https://doi.org/10.3934/dcds.2023001; read in arXiv:2203.00434v2 (Section 2 of arXiv:2203.00434v2, for the decidability of the domino problem on $\mathbb{Z}$ and its undecidability on $\mathbb{Z}^d$, $d \ge 2$).
