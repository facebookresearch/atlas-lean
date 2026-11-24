# Chao's lower bound for species richness

Chao's estimator of the number $\Delta$ of species missed by a limited sample of a large community is $\hat\Delta = f_1^2/(2 f_2)$, where $f_1$ and $f_2$ are the numbers of species seen exactly once and twice (Béguinot 2014, equation (1)); it is commonly read as a lower bound. The lower-bound property is exact in expectation under Poisson sampling. Suppose the community has $S$ species and species $i$ is observed $N_i \sim \mathrm{Poisson}(\lambda_i)$ times independently, $\lambda_i > 0$, and let $f_k$ be the number of species observed exactly $k$ times. Then $E[f_k] = \sum_i e^{-\lambda_i}\lambda_i^k/k!$, and the Cauchy–Schwarz inequality $\bigl(\sum_i e^{-\lambda_i}\lambda_i\bigr)^2 \le \bigl(\sum_i e^{-\lambda_i}\bigr)\bigl(\sum_i e^{-\lambda_i}\lambda_i^2\bigr)$ gives $E[f_1]^2 \le 2\, E[f_0]\, E[f_2]$, so
$$S = E[S_{\mathrm{obs}}] + E[f_0] \ge E[S_{\mathrm{obs}}] + \frac{E[f_1]^2}{2\, E[f_2]}, \qquad S_{\mathrm{obs}} = S - f_0,$$
with equality exactly when all $\lambda_i$ are equal.

## Expansion

1. The Poisson sampling model with heterogeneous rates, and the expected frequency counts.
2. The Cauchy–Schwarz step and its equality case.
3. The lower bound for $S$, and the plug-in estimator $S_{\mathrm{obs}} + f_1^2/(2 f_2)$.
4. The bias-corrected form $f_1(f_1 - 1)/(2(f_2 + 1))$ when $f_2 = 0$, and the multinomial-sampling approximation, as separate statements.
5. The species-abundance distributions under which Chao's estimator is centred, as derived by Béguinot, as a separate statement.

## Sources

- J. Béguinot, An algebraic derivation of Chao's estimator of the number of species in a community highlights the condition allowing Chao to deliver centered estimates, Int. Sch. Res. Notices 2014 (2014), 847328, equation (1). <https://doi.org/10.1155/2014/847328>
- Original result: A. Chao, Nonparametric estimation of the number of classes in a population, Scand. J. Statist. 11 (1984), 265–270. The estimator f1^2/(2 f2) follows Béguinot (2014).
