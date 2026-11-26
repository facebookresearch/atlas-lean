# Interval and remaining lifetime risk from annual transition probabilities

**Model.** Individuals move among finitely many health states (for example healthy, hypertension, hyperlipidemia, diabetes, combinations of these, coronary artery disease, death). For individual $i$ in state $j$ at integer age $a$, the probability of being in state $k \ne j$ one year later is

$$\pi_{jkia} = \operatorname{logit}^{-1}\!\big(\beta_{jk a}^{\top} z_{ia}\big),$$

a logistic regression on time-invariant covariates (sex, polygenic risk score) and time-dependent covariates (smoking, antihypertensive or statin use) $z_{ia}$, with coefficients $\beta_{jka}$ estimated separately for each age and each transition and then smoothed across ages. The probability of remaining in $j$ is the complement

$$\pi_{jjia} = 1 - \sum_{k\ne j}\pi_{jkia}.$$

These define an age-inhomogeneous Markov chain whose transition probabilities depend on the current state and covariates but not on earlier states.

**Risk functionals.** The predicted risk of progressing from $j$ to $k$ between ages $A_1$ and $A_2$ is

$$\mathrm{IntervalRisk}_{jki}(A_1,A_2) = 1 - \prod_{a=A_1}^{A_2}\big(1-\pi_{jkia}\big),$$

the remaining lifetime risk is the same expression with $A_2 = L$, the maximal age considered, and the risk under a treatment with constant per-year relative risk reduction $\mathrm{RR}$ applied to each annual transition is

$$\mathrm{IntervalRisk}^{\mathrm{treated}}_{jki}(A_1,A_2) = 1 - \prod_{a=A_1}^{A_2}\big(1-(1-\mathrm{RR})\,\pi_{jkia}\big).$$

The absolute risk reduction from treatment is the difference of the untreated and treated interval risks.

## Depends on

- [State distribution in a discrete-time multistate life table](../../../population-dynamics/life-tables/multistate-life-table-by-matrix-products.md)

## Remarks

The product $\prod_a(1-\pi_{jkia})$ is the probability of not making the $j\to k$ move in any year of the interval when the annual moves are treated as conditionally independent given covariates, so its complement is the cumulative risk. Because the coefficients $\beta_{jka}$ vary freely with age, the model needs no parametric covariate-by-time interaction, and the remaining lifetime risk can be recomputed every year as covariates change; this is why remaining lifetime risk can fall with age (fewer years remain) even while ten-year risk rises. The product formula conditions on the starting state; when competing exits from $j$ (to other risk-factor states or death) matter, the exact probability of ever reaching $k$ is an entry of the product of the full annual transition matrices, as in a multistate life table. Fitting each transition by its own binary logistic regression and closing the row by complement approximates a polytomous regression at much lower computational cost when staying in $j$ is the dominant outcome. Because a constant relative reduction shrinks every annual probability, the absolute benefit of treatment over a long horizon is largest for young individuals with high genetic risk even when their ten-year risk is similar to that of older, low-risk individuals.

## Sources

- S. M. Urbut, M. W. Yeung, S. Khurshid, S. M. J. Cho, A. Schuermans, J. German, K. Taraszka, K. Paruchuri, A. C. Fahed, P. T. Ellinor et al., "MSGene: a multistate model using genetic risk and the electronic health record applied to lifetime risk of coronary artery disease", Nature Communications 15 (2024), Results "Novel multistate model with time-dependent transitions" and "Model interpretation", and Methods "Predicted interval risk", Eqs. (4)–(7), <https://doi.org/10.1038/s41467-024-49296-9>, PMCID PMC11161589.
