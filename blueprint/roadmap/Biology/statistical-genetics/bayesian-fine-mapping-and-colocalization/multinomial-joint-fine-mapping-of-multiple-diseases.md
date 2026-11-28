# Multinomial joint fine-mapping of multiple diseases

Let $d$ diseases be studied in one genomic region with a shared control group, and let each individual belong to exactly one of the groups controls, disease $1,\dots,$ disease $d$. A **configuration** is a tuple $(M_1,\dots,M_d)$ of causal-variant models, $M_j$ being a set of SNPs causal for disease $j$. Multinomial fine-mapping (MFM) models group membership by multinomial logistic regression on the SNPs of the configuration and places a prior on configurations that couples the diseases. For two diseases, let the region contain $n$ SNPs and let the marginal model priors $\pi_1,\pi_2$ depend on a model only through its size, as in the source. Then

$$\pi(M_1,M_2)\;=\;\pi_1(M_1)\,\pi_2(M_2)\,\tau(|M_1|,|M_2|)\times\begin{cases}\kappa,&M_1\cap M_2\ne\varnothing,\\1,&\text{otherwise},\end{cases}$$

so configurations sharing at least one causal variant are upweighted by $\kappa\ge1$. The normalization factor $\tau$ is chosen so that the total prior mass on configurations with given model sizes $|M_1| = m$, $|M_2| = l$ does not depend on $\kappa$:

$$\sum_{|M_1|=m,\ |M_2|=l}\pi_1(M_1)\,\pi_2(M_2)\;=\;\sum_{|M_1|=m,\ |M_2|=l}\pi_1(M_1)\,\pi_2(M_2)\,\tau(m,l)\,\kappa^{\mathbf 1[M_1\cap M_2\ne\varnothing]}.$$

Of the $\binom nm\binom nl$ pairs with these sizes, $\binom nm\binom{n-m}l$ are disjoint, so

$$\tau(m,l)\;=\;\frac{\binom nl}{\binom{n-m}l+\kappa\left(\binom nl-\binom{n-m}l\right)}.$$

In particular $\tau = 1$ when $\kappa = 1$, and the coupled prior has total mass $1$ whenever $\pi_1$ and $\pi_2$ do. $\kappa$ is calibrated from a prior probability that a pair of associated diseases shares a causal variant (taken as $0.5$). Two approximations make the search tractable after per-disease stochastic search:

1. the log Bayes factor of a configuration under the multinomial model is approximately the sum of the per-disease logistic log Bayes factors plus an offset determined by sample and model sizes; when diseases do not share controls the joint log Bayes factor is exactly that sum;
2. the marginal posterior of each disease's model, $P(M_j\mid\text{data})$, can be computed from these quantities without storing the Bayes factors of all configurations, whose number is the product of the per-disease model counts.

## Remarks

Sharing controls between case series correlates the per-disease logistic regressions; the multinomial likelihood accounts for this exactly, and the additive approximation recovers most of its information at the cost of per-disease fits. The coupling prior plays the role of the colocalization prior: shared causal variants pool evidence across diseases, which acts like a larger sample when sharing is real, while with strong disease-specific signals or no signal in one disease the joint analysis neither gains nor misleads, as the simulations in the paper show. Stochastic search over models, rather than stepwise selection, matters because stepwise search can first select a SNP that tags two correlated causal variants and then miss both.

## Sources

- J. L. Asimit, D. B. Rainbow, M. D. Fortune et al., "Stochastic search and joint fine-mapping increases accuracy and identifies previously unreported associations in immune-mediated diseases", Nat. Commun. 10 (2019), Results ("Proposed method for fine-mapping multiple diseases", "MFM increases chance of selecting the correct model") and Supplementary Note 3 (Section 3.2, Eqs. (13)–(14), the configuration prior with model-size normalization $\tau_{ij}$), <https://doi.org/10.1038/s41467-019-11271-0>, PMCID PMC6642100.
