# Case–control ancestry composition under subpopulation-specific risk

**Model.** A population consists of $N$ subpopulations. An individual drawn from the study base belongs to subpopulation $i$ with probability $P(i)$, $\sum_{i=1}^N P(i) = 1$, and has the disease with probability $P(d = c \mid i)$. Cases and controls are sampled from the diseased and non-diseased individuals respectively.

**Statement** (O'Connor et al. 2013, Materials and Methods, "Methodological Theory for Confounding", eqs. (1)–(3)). By Bayes' theorem the subpopulation composition of the cases is

$$P(i \mid c) = \frac{P(d = c \mid i)\, P(i)}{P(c)}, \qquad P(c) = \sum_{j=1}^{N} P(d = c \mid j)\, P(j),$$

and that of the controls, $P(i \mid \bar c)$, is obtained by replacing $P(d = c \mid i)$ with $1 - P(d = c \mid i)$. A sample of $m$ cases contains in expectation $n_{c \mid i} = m\, P(i \mid c)$ cases from subpopulation $i$, and likewise for controls. The case and control samples have the same composition, for every choice of $P(i)$, if and only if the disease risk is the same in all subpopulations with $P(i) > 0$.

## Depends on

- [Bayes' rule for countably many hypotheses](../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/bayes-rule/bayes-posterior-apply-singleton.md): the subpopulation composition of cases and of controls

## Expansion

If $P(d = c \mid i) = \kappa$ for all $i$ then $P(c) = \kappa$ and $P(i \mid c) = P(i \mid \bar c) = P(i)$. Conversely, $P(i \mid c)/P(i \mid \bar c)$ is proportional to the odds $P(d = c \mid i)/(1 - P(d = c \mid i))$, so equal compositions force equal odds and hence equal risks. When the compositions differ, a variant with subpopulation allele frequencies $f_i$ has expected case and control frequencies $\sum_i P(i \mid c) f_i$ and $\sum_i P(i \mid \bar c) f_i$, which differ whenever the frequency differences line up with the risk differences, giving a spurious association with no causal effect. Rare variants tend to be young and geographically restricted, so their $f_i$ can differ sharply even between closely related subpopulations, and tests that collapse many such variants inherit these differences. In the study's simulations the risks and sampling proportions were varied symmetrically around $P(d = c \mid i) = 0.03$ and $P(i) = 0.2$ across five European-like subpopulations, the case of equal values being the no-confounding control.

## Sources

- T. D. O'Connor, A. Kiezun, M. Bamshad et al., "Fine-scale patterns of population stratification confound rare variant association tests", PLoS ONE 8 (2013), e65834, Materials and Methods, eqs. (1)–(3), <https://doi.org/10.1371/journal.pone.0065834>, PMCID PMC3701690.
