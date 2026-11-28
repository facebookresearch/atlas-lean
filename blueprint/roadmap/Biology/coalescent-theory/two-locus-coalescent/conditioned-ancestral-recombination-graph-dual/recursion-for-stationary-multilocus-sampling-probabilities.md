# Recursion for stationary multilocus sampling probabilities with recombination

In the multilocus Wright–Fisher diffusion with mutation rates $\theta_l$ (transition matrices $P^{(l)}$ with stationary laws $\mu^{(l)}$) and recombination rates $\rho_l$ between loci $l$ and $l+1$ of the [typed ARG dual](typed-arg-dual-of-the-multilocus-wright-fisher-diffusion.md), let $\widetilde m(\mathbf n)$ be the stationary moment indexed by a configuration $\mathbf n = (n^A_{\mathbf i})$ of $n$ partially specified haplotypes, with $n^A = \sum_{\mathbf i \in E_A} n^A_{\mathbf i}$.

**Proposition.** For every configuration $\mathbf n$ of size $n$,

$$\Big[n(n-1) + \sum_{l=1}^L \theta_l \sum_{A \ni l} n^A + \sum_{l=1}^{L-1} \rho_l \sum_{A:\,A_{\le l}\ne\emptyset\ne A_{>l}} n^A\Big]\widetilde m(\mathbf n) = \sum_{\emptyset\ne A\subseteq[L]}\Big[\sum_{\emptyset \ne B}\sum_{\mathbf i\in E_{A\cup B}} n^A_{\mathbf i}(n^B_{\mathbf i} - \delta_{AB})\,\widetilde m(\mathbf n - \mathbf e^A_{\mathbf i} - \mathbf e^B_{\mathbf i} + \mathbf e^{A\cup B}_{\mathbf i})$$

$$+ \sum_{\mathbf i\in E_A}\sum_{l\in A}\theta_l\sum_{j\in E_l} P^{(l)}_{j i_l}\, n^A_{\mathbf i}\,\widetilde m(\mathbf n - \mathbf e^A_{\mathbf i} + \mathbf e^A_{\mathbf i[l\to j]}) + \sum_{\mathbf i\in E_A}\sum_{l=\min A}^{\max A - 1}\rho_l\, n^A_{\mathbf i}\,\widetilde m(\mathbf n - \mathbf e^A_{\mathbf i} + \mathbf e^{A_{\le l}}_{\mathbf i} + \mathbf e^{A_{>l}}_{\mathbf i})\Big],$$

with boundary condition $\widetilde m(\mathbf e^{\{1\}}_{i_1} + \dots + \mathbf e^{\{L\}}_{i_L}) = \prod_{l=1}^L \mu^{(l)}_{i_l}$ (single-locus lineages at distinct loci are independent and in mutational equilibrium).

The left side is the total event rate (coalescence, mutation at an ancestral locus, recombination splitting an ancestral segment); each term on the right is a configuration reached by one event. Together with the boundary condition this is a linear system for the stationary multilocus sampling probabilities, the multilocus analogue of the Griffiths–Marjoram recursion for the ancestral recombination graph.

## Depends on

- [Typed ARG dual of the multilocus Wright–Fisher diffusion with recombination](typed-arg-dual-of-the-multilocus-wright-fisher-diffusion.md)

## Expansion

Take expectations of $\mathcal L \widetilde Q(\mathbf X_\infty,\mathbf n)$ under the stationary law, where it vanishes: the drift and diffusion terms of the generator map each monomial to monomials of the neighbouring configurations, and collecting coefficients gives the displayed identity. Coalescence reduces the number of lineages, mutation preserves it, and recombination increases it only by splitting a set of ancestral loci into two nonempty parts.

## Sources

- Robert C. Griffiths, Paul A. Jenkins and Sabin Lessard, *A coalescent dual process for a Wright–Fisher diffusion with recombination and its application to haplotype partitioning*, Theor. Popul. Biol. 112 (2016), 126–138. <https://doi.org/10.1016/j.tpb.2016.08.007> Proposition 1. Corrigendum: Theor. Popul. Biol. 130 (2019), 203. <https://doi.org/10.1016/j.tpb.2019.08.001> Locators use the numbering of the preprint arXiv:1604.04145. Its latest version corrects typographical errors in equations (25)–(27), (B.3) and (B.4).
