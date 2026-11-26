# Beta-uniform mixture log-likelihood-ratio node score

**Aggregating several p-values.** If a gene has $n$ p-values $X_1, \dots, X_n$ from independent tests (for example differential expression and survival association) that are i.i.d. uniform on $(0,1)$ under the null, then its $i$-th order statistic satisfies

$$X_{(i)} \sim \mathrm{Beta}(i,\ n - i + 1), \qquad \Pr\big(X_{(i)} \le x\big) = \sum_{l = i}^{n} \binom{n}{l} x^{l}(1 - x)^{n - l},$$

so this cumulative distribution function evaluated at the observed $X_{(i)}$ is a single "p-value of p-values" per gene; with missing values $n$ is replaced by the number observed.

**Signal–noise decomposition.** The aggregated p-values $x_1, \dots, x_m$ of all $m$ network nodes are modelled by the beta-uniform mixture

$$f(x \mid \lambda, a) = \lambda + (1 - \lambda)\, a\, x^{a - 1}, \qquad 0 < x \le 1,\ 0 \le \lambda \le 1,\ 0 < a < 1,$$

a uniform noise component with weight $\lambda$ and a $\mathrm{Beta}(a, 1)$ signal component; $(\hat\lambda, \hat a)$ maximize $\sum_{l} \log f(x_l \mid \lambda, a)$.

**Score.** The log-likelihood ratio of signal to noise at $x$ is $\log(a x^{a-1}/1)$; shifting it to vanish at a significance threshold $\tau$ gives the additive node score

$$S(x) = \log\frac{a x^{a - 1}}{a \tau^{a - 1}} = (a - 1)\big(\log x - \log \tau\big),$$

which is positive exactly when $x < \tau$ (because $a < 1$) and negative for $x > \tau$. The threshold is chosen so that the estimated false discovery rate among nodes with $x \le \tau$ equals a target $\mathrm{FDR}$; using the Pounds–Morris upper bound $\hat\pi = \lambda + (1 - \lambda)a$ on the null proportion, $\widehat{\mathrm{FDR}}(\tau) = \hat\pi\tau / F(\tau)$ with $F(\tau) = \lambda\tau + (1 - \lambda)\tau^{a}$, which gives

$$\tau(\mathrm{FDR}) = \left(\frac{\hat\pi - \mathrm{FDR}\cdot\lambda}{\mathrm{FDR}\,(1 - \lambda)}\right)^{1/(a - 1)} .$$

A subnetwork's score is the sum of its node scores.

**Properties.**

- As $a \to 1$ the signal density tends to the uniform, and $S(x) \to 0$ for all $x$: with no detectable signal, even very small p-values score zero (in the source, fitting purely random p-values gave $\lambda = 1$, $a = 1$ and all-zero scores).
- As $\tau \to 0$, $S(x) \to -\infty$ for each fixed $x$; as $\tau \to 1$ all scores become positive.
- If the threshold makes the expected node score negative, the expected score of a random subnetwork decreases linearly in its size, which (as for local sequence alignment) is what makes maximal-scoring subnetworks local rather than spanning the network.

## Expansion

The order-statistic law follows because $X_{(i)} \le x$ iff at least $i$ of the $n$ uniform values fall below $x$. The mixture likelihood is maximized numerically (L-BFGS-B in the source, giving $\hat\lambda \approx 0.54$ and $\hat a \approx 0.28$ for the lymphoma data). The threshold formula solves $\hat\pi\tau / (\lambda\tau + (1 - \lambda)\tau^{a}) = \mathrm{FDR}$ for $\tau$: dividing by $\tau$ gives $\hat\pi / \mathrm{FDR} = \lambda + (1 - \lambda)\tau^{a - 1}$. The score is a likelihood ratio test statistic shifted by the constant $(a - 1)\log\tau$, so adjusted and unadjusted scores differ by an additive offset, and the single parameter FDR controls module size.

## Sources

- M. T. Dittrich, G. W. Klau, A. Rosenwald, T. Dandekar, T. Müller, "Identifying functional modules in protein–protein interaction networks: an integrated exact approach", Bioinformatics (2008), Section 3.1 (3.1.1 order statistics of p-values, Eqs. (1)–(2); 3.1.2 signal–noise decomposition and adjusted log-likelihood-ratio score, Eq. (3)), <https://doi.org/10.1093/bioinformatics/btn161> (PMC2718639).
