# Sample complexity of ASTRAL-one under the DLCoal model

**Method.** Given $k$ multi-labelled gene trees $t_1,\dots,t_k$ on species set $S$ with $|S|=n$, ASTRAL-one keeps one uniformly random copy per species in each $t_i$, giving $\tilde t_i$, and returns the species tree $\widetilde T$ maximizing the quartet score

$$Q_k(\widetilde T)=\sum_{i=1}^k\ \sum_{\mathcal J=\{a,b,c,d\}}\mathbf 1\big(\widetilde T_{ext}^{\mathcal J},\tilde t_i^{\mathcal J}\big),$$

where $\widetilde T_{ext}$ attaches all copies of a species at its leaf.

**Theorem.** Suppose gene trees are generated i.i.d. under the DLCoal model (duplication rate $\lambda$, loss rate $\mu\ne\lambda$) on a species tree with finite minimum branch length $f$ (coalescent units) and depth $\Delta$. For every $\epsilon>0$ there are universal constants $C,C'>0$ such that exact ASTRAL-one returns the true unrooted species tree with probability at least $1-\epsilon$ whenever

$$k\ \ge\ C'\,\frac1{f^2}\,\frac{e^{C|\mu-\lambda|\Delta}}{\big(1-\frac\lambda\mu\wedge\frac\mu\lambda\big)^{C}}\,\log\frac n\epsilon .$$

Concretely, $k\ge\dfrac{2304\,\alpha^6}{\sigma^7\gamma^2}\log\dfrac n\epsilon$ suffices, with $\gamma=1-e^{-f}$, $\sigma$ the worst quartet survival probability and $\alpha$ the largest expected number of copies at a species-tree vertex.

The bound grows both in the subcritical regime ($\mu/\lambda$ large: species often have no copy) and in the supercritical regime ($\lambda/\mu$ large: many copies at the ancestor of a quartet create conflicting gene quartets).

## Depends on

- [Quantitative quartet gap under the DLCoal model](quantitative-quartet-gap-under-the-dlcoal-model.md)

## Expansion

ASTRAL-one recovers the species tree if, for every quartet of species, the species quartet is the most frequent topology among gene trees in which all four species have a copy. By Hoeffding's inequality, with probability $1-\epsilon$ every quartet is informative in at least $k^*\approx k\sigma/2$ gene trees once $k\ge(2k^*/\sigma)\vee(8\sigma^{-2}\log(n/\epsilon))$. A union bound over the at most $n^4$ quartets, using the gap $\delta'$ between the probability of the true quartet and $1/3$, shows that $k^*>8\log(n/\epsilon)/\delta'^2$ informative trees suffice. Inserting $\delta'\ge\frac23(\gamma\wedge\frac18)\sigma^3/\alpha^3$ and the branching-process bounds on $\sigma$ and $\alpha$, and $\gamma\ge c f$ for small $f$, gives the displayed rate.

## Sources

- M. Hill, B. Legried, S. Roch, "Species tree estimation under joint modeling of coalescence and duplication: sample complexity of quartet methods", arXiv:2007.06697 (2020), <https://doi.org/10.48550/arXiv.2007.06697>. Section 2.2 (Theorem 1) and Section 4 (Lemmas 13–17 and the final analysis).
