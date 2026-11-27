# Multiplicative epistasis equals the natural parameters of a multivariate Bernoulli distribution

**Setting.** For $L$ biallelic loci, a genotype is $x \in \{0,1\}^L$ and has fitness $f_x$, a real number, positive for Theorem 1 and for the multiplicative measure; for $T \subseteq \{1,\dots,L\}$ write $f_T$ for the fitness of the genotype mutated exactly at $T$ ($f_\emptyset$ is the wild type). The *multiplicative epistasis measure* of a set $S$ of loci, $|S| \ge 1$, is defined through its logarithm, the alternating sum

$$\log \epsilon_S^{M} = \sum_{T \subseteq S} (-1)^{|S| - |T|}\,\log f_T ,$$

so that for a pair $\log \epsilon^M_{ij} = \log f_{ij} - \log f_i - \log f_j + \log f_\emptyset$, i.e. $\epsilon^M_{ij} = f_{ij}/(f_i f_j)$ when $f_\emptyset = 1$. The *additive measure* $\epsilon_S^{A}$ is the same alternating sum applied to $f$ itself.

A random vector $X = (X_1,\dots,X_L) \in \{0,1\}^L$ with $p_x = \Pr(X = x) > 0$ is multivariate Bernoulli; its *natural parameters* $\beta = (\beta_S)_{S \subseteq \{1,\dots,L\}}$ are defined by the log-linear representation

$$\log p_x = \sum_{S \subseteq \mathrm{supp}(x)} \beta_S .$$

**Theorem 1.** If $f_x = c\,p_x$ for some constant $c > 0$ and some MVB distribution $p$, then for every non-empty $S$, $\log \epsilon_S^{M} = \beta_S$.

**Corollary 1.** Let the fitness values be real numbers, not necessarily positive. If $f_x = c\log p_x$ for some $c > 0$ and some MVB distribution $p$ (so every $f_x$ is negative), then the additive measure, the same alternating sum applied to $f$, equals $c\,\beta_S$ for every non-empty $S$ (equal to $\beta_S$ on the normalised scale $c = 1$).

## Depends on

- [Haploid selection and the crossproduct ratio: epistasis generates linkage disequilibrium](../../population-genetics/haploid-selection-and-multiplicative-fitnesses/epistasis-generates-linkage-disequilibrium.md)

## Proof depends on

- [Möbius inversion formula](../../../Order/ordered-sets/incidence-algebras-and-the-m-bius-function/moebius-inversion-iff.md)

## Expansion

The log-linear representation is a Möbius transform over the Boolean lattice of subsets: $\log p_{1_T} = \sum_{S \subseteq T}\beta_S$, where $1_T$ is the indicator genotype of $T$. Möbius inversion gives $\beta_S = \sum_{T \subseteq S}(-1)^{|S|-|T|}\log p_{1_T}$. Replacing $\log p_{1_T}$ by $\log f_T - \log c$ changes nothing for $|S| \ge 1$, because $\sum_{T \subseteq S}(-1)^{|S|-|T|} = 0$; this is exactly the multiplicative measure. Consequently $\beta_S$, the interaction term for $S$ in a log-linear (Poisson or logistic) regression, is the same object as multiplicative epistasis, and $\beta_{ij} = 0$ for all pairs in a set of loci characterises conditional-independence structure of the MVB. In case–control GWAS, the SNP×SNP interaction term of a logistic regression of disease status on two loci equals a three-way natural parameter $\beta_{ijk}$ of the MVB on $(X_i, X_j, \text{disease})$.

## Sources

- U. Chitra, B. Arnold, B. J. Raphael, "Resolving discrepancies between chimeric and multiplicative measures of higher-order epistasis", Nature Communications (2025), Theorem 1, Corollary 1, Eq. (2) and Methods, <https://doi.org/10.1038/s41467-025-56986-5>, PMCID PMC11833126.
