# Logistic boosting step with additive and genotype-specific variant scores

**Setting.** Individuals $i = 1,\dots,N$ have disease status $y_i \in \{+1,-1\}$ and genotypes $G(x_i) \in \{0,1,2\}$ (minor-allele count) at each candidate variant; $F_t(x)$ is the current log-odds score, initialized at a covariate-only logistic fit. At iteration $t$ set

$$p_{t,i} = \frac{1}{1+e^{-F_t(x_i)}}, \qquad z_{t,i} = \begin{cases} 1/p_{t,i} & y_i = +1 \\ -1/(1-p_{t,i}) & y_i = -1\end{cases}, \qquad w_{t,i} = p_{t,i}(1-p_{t,i}),$$

and, for a variant, $W_k = \sum_{i:G(x_i) = k} w_{t,i}$ and $U_k = \sum_{i: G(x_i) = k} w_{t,i}z_{t,i}$, $k = 0,1,2$.

**Proposition (optimal variant scores).** Minimizing the weighted squared loss $\sum_i w_{t,i}\big(f(x_i) - z_{t,i}\big)^2$ over
1. *additive scores* $f(x) = c + \alpha\,G(x)$ gives

$$c = \frac{(W_1 + 4W_2)U_0 + 2W_2U_1 - W_1U_2}{W_0W_1 + W_1W_2 + 4W_0W_2}, \qquad \alpha = \frac{-(W_1 + 2W_2)U_0 + (W_0 - W_2)U_1 + (2W_0 + W_1)U_2}{W_0W_1 + W_1W_2 + 4W_0W_2};$$

2. *genotype-specific (non-additive) scores* $f(x) = s_{G(x)}$ gives $s_k = U_k/W_k$.

The boosting step selects the variant with the smallest minimized loss and updates $F_{t+1} = F_t + \gamma f_t$ with learning rate $0 < \gamma \le 1$.

## Depends on

- [Negative log-likelihood of logistic regression](../../../../ComputerScience/machine-learning/supervised-learning/logistic-regression-and-support-vector-machines/logistic-nll.md)

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

The working response and weights are those of a Newton (iteratively reweighted least squares) step for the logistic log-likelihood, so each iteration fits the best single-variant correction to the log-odds. The loss depends on the data only through $(W_k,U_k)$; for the additive model the normal equations $c\sum_kW_k + \alpha\sum_k kW_k = \sum_kU_k$ and $c\sum_k kW_k + \alpha\sum_k k^2W_k = \sum_k kU_k$ have determinant $W_0W_1 + W_1W_2 + 4W_0W_2$, and for the non-additive model each genotype class is fitted separately by its weighted mean. The triplet $(s_0,s_1,s_2)$ classifies the inferred mode of inheritance (additive, dominant, recessive, heterozygote-specific); in practice the homozygous-minor score is regularized because few individuals carry it.

## Sources

- R. Ohta, Y. Tanigawa, Y. Suzuki, M. Kellis, S. Morishita, "A polygenic score method boosted by non-additive models", Nature Communications 15 (2024) 4433, Methods (overview of the GenoBoost algorithm), Algorithm 1, Eqs (1)–(7), <https://doi.org/10.1038/s41467-024-48654-x>, PMCID PMC11522481.
