# $Q_{ST}$ equals $F_{ST}$ for a neutral additive trait

Consider a diploid quantitative trait determined additively by $n$ loci with no dominance or epistasis: locus $\ell$ has a reference allele with additive effect $a_\ell$ per copy, and its frequency in a population is $p_\ell$. Populations derive from a common ancestral population in which the allele frequencies are $\bar p_\ell$, and the frequencies drift neutrally and independently across loci, with

$$\mathbb{E}[p_\ell] = \bar p_\ell, \qquad \operatorname{Var}(p_\ell) = F_{ST}\, \bar p_\ell (1 - \bar p_\ell)$$

for a common $F_{ST} \in [0, 1)$ (the same drift acts on every locus, whatever its effect on the trait). Assume Hardy–Weinberg and linkage equilibrium within populations. Let $V_B$ be the variance among populations of the population mean trait value and $V_W$ the expected additive genetic variance within a population, and put

$$A = \sum_\ell 4a_\ell^2\, \bar p_\ell(1 - \bar p_\ell).$$

Then

$$V_B = F_{ST}\, A, \qquad 2V_W = (1 - F_{ST})\, A.$$

If moreover $A > 0$ (some locus with $a_\ell \ne 0$ segregates in the ancestral population), then $V_B + 2V_W = A > 0$ and

$$Q_{ST} := \frac{V_B}{V_B + 2V_W} = F_{ST}.$$

If $A = 0$, then $V_B = V_W = 0$ and $Q_{ST}$ is undefined.

## Proof sketch

The mean trait value of a population is $\sum_\ell 2a_\ell p_\ell$ up to a constant, so by independence across loci $V_B = \sum_\ell 4a_\ell^2 F_{ST}\, \bar p_\ell(1-\bar p_\ell)$. The additive variance within a population is $\sum_\ell 2a_\ell^2 p_\ell(1-p_\ell)$, and $\mathbb{E}[p_\ell(1-p_\ell)] = \bar p_\ell - \bar p_\ell^2 - \operatorname{Var}(p_\ell) = (1 - F_{ST})\bar p_\ell(1-\bar p_\ell)$, so $V_W = \sum_\ell 2a_\ell^2 (1-F_{ST})\, \bar p_\ell(1-\bar p_\ell)$. Hence $V_B = F_{ST} A$ and $2V_W = (1 - F_{ST})A$, and when $A > 0$ dividing gives $Q_{ST} = F_{ST}$, independently of the number of loci and of their effect sizes. Because drift moves every locus by the same random process regardless of the size and sign of its trait contribution, phenotypic differences among populations are expected under neutrality to be of the same order as typical single-locus differences. A trait with $Q_{ST}$ well above $F_{ST}$ suggests divergent selection, and one well below suggests uniform stabilizing selection; for polygenic scores the corresponding null is the neutral drift model of population genetic values.

## Depends on

- [Hardy–Weinberg proportions](../../../population-genetics/hardy-weinberg-law/offspring-apply.md)

## Sources

- N. A. Rosenberg, M. D. Edge, J. K. Pritchard and M. W. Feldman, Interpreting polygenic scores, polygenic adaptation, and human phenotypic differences, *Evol. Med. Public Health* 2019 (2019), 26–34, <https://doi.org/10.1093/emph/eoy036>, PMCID PMC6393779 (section "Polygenic adaptation: the null expectation").
- R. Lande, Neutral theory of quantitative genetic variance in an island model with local extinction and colonization, *Evolution* 46 (1992), 381–389, <https://doi.org/10.1111/j.1558-5646.1992.tb02046.x>.
- M. C. Whitlock, Neutral additive genetic variance in a metapopulation, *Genet. Res.* 74 (1999), 215–221, <https://doi.org/10.1017/S0016672399004127>.
