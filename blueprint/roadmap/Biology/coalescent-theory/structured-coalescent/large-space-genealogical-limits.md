# Genealogies of samples from a large torus

For spatial population models on a torus of side $L$, genealogies of samples taken far apart converge, on a time scale that grows with $L$, to non-spatial coalescents. Berestycki (2009, Section 5.1.4) states the following results for the stepping-stone model on the two-dimensional torus $(\mathbb Z/L)^2$, with $N$ individuals per colony, migration probability $\nu$ and a symmetric migration kernel of variance $\sigma^2$ per coordinate. For two lineages started uniformly, the time $T_0$ until they occupy one colony satisfies $P\bigl(T_0 > t\,L^2\log L/(2\pi\sigma^2\nu)\bigr) \to e^{-t}$ as $L \to \infty$ and $\nu \to 0$, and the further time to coalescence has mean $NL^2$ (Theorem 5.6, due to Cox and Durrett). If $2N\nu\pi\sigma^2/\log L \to \alpha$, the coalescence time $t_0$ satisfies $P\bigl(t_0 > (1 + \alpha)t\,L^2\log L/(2\pi\sigma^2\nu)\bigr) \to e^{-t}$ (Theorem 5.7), and the ancestral partition of $k$ sampled individuals, with time scaled by $h_L = (1 + \alpha)L^2\log L/(2\pi\sigma^2\nu)$, converges to Kingman's $k$-coalescent (Theorem 5.8, due to Zähle, Cox and Durrett). In dimension $d \ge 3$, the spatial $\Lambda$-coalescent on a torus of side $2N + 1$, run on the time scale $(2N + 1)^d$, converges to Kingman's coalescent at speed $\kappa = 2/(G + 2/\lambda_{2,2})$, started from the eventual partition on $\mathbb Z^d$, where $G$ is the expected number of visits to the origin of simple random walk (Theorem 5.10, due to Limic and Sturm). For the spatial $\Lambda$-Fleming–Viot process on a two-dimensional torus, Barton, Etheridge and Véber (2010, Theorems 3.3 and 3.7) obtain, depending on how often large reproduction events occur, Kingman or $\Lambda$-coalescent limits for the genealogy of a sample, and in the regime of Theorem 3.7(a) a spatial limit that is neither; in the regime of Proposition 6.2(b) the gathering times are of order $L^2\log L$.

## Depends on

- [Rate matrix of Kingman's partition-valued coalescent](../partition-valued-kingman-coalescent/partition-rate.md)

## Expansion

1. The stepping-stone model on $(\mathbb Z/L)^2$ and its ancestral lineages as continuous-time random walks with kernel $q$.
2. The meeting-time asymptotics for two lineages via the local central limit theorem (Theorem 5.6), and the two regimes for the coalescence time (Corollary 5.1, Theorem 5.7).
3. The Kingman limit of the ancestral partition of a sample (Theorem 5.8).
4. The spatial $\Lambda$-coalescent on large tori in $d \ge 3$ and the constant $\kappa$ (Theorem 5.10).
5. The spatial $\Lambda$-Fleming–Viot limits with small and large events (Theorems 3.3 and 3.7 of Barton, Etheridge and Véber), including the spatial limit of Theorem 3.7(a).

## Sources

- N. Berestycki, *Recent Progress in Coalescent Theory*, Ensaios Matemáticos 16, Sociedade Brasileira de Matemática, 2009, Sections 5.1.4 and 5.2.2, Theorems 5.6–5.8 and 5.10. <https://arxiv.org/abs/0909.3985>
- N. H. Barton, A. M. Etheridge and A. Véber, A new model for evolution in a spatial continuum, Electron. J. Probab. 15 (2010), 162–216, Section 3 (Theorems 3.3 and 3.7) and Proposition 6.2. <https://doi.org/10.1214/ejp.v15-741>
- Original result: J. T. Cox and R. Durrett, The stepping stone model: new formulas expose old myths, Ann. Appl. Probab. 12 (2002), 1348–1377. <https://doi.org/10.1214/aoap/1037125866> The meeting-time statement follows Berestycki (2009), Theorem 5.6.
- Original result: I. Zähle, J. T. Cox and R. Durrett, The stepping stone model. II: Genealogies and the infinite sites model, Ann. Appl. Probab. 15 (2005), 671–699. <https://doi.org/10.1214/105051604000000701> The Kingman limit follows Berestycki (2009), Theorem 5.8.
- Original result: V. Limic and A. Sturm, The spatial Λ-coalescent, Electron. J. Probab. 11 (2006), 363–393. <https://doi.org/10.1214/EJP.v11-319> The torus limit follows Berestycki (2009), Theorem 5.10.
