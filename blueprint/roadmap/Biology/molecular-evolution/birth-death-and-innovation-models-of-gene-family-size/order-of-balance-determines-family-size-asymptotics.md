# Order of balance determines family-size asymptotics

Consider the master birth, death and innovation model (BDIM) with birth rates $\lambda_i$ and death rates $\delta_i$ and its equilibrium frequencies $p_i$, as in [equilibrium of the BDIM](equilibrium-of-the-birth-death-and-innovation-model.md). Assume that for large $i$

$$\chi(i) := \frac{\lambda_{i-1}}{\delta_i} = i^{s}\,\theta\left(1 + \frac{a}{i} + O\!\left(\frac{1}{i^2}\right)\right), \qquad s, a \in \mathbb{R},\ \theta > 0.$$

Call the model **non-balanced** if $s \ne 0$; **first-order balanced** if $s = 0$, $\theta \ne 1$; **second-order balanced** if $s = 0$, $\theta = 1$, $a \ne 0$; and **high-order balanced** if $s = 0$, $\theta = 1$, $a = 0$. Write $q_i \sim r_i$ when $q_i / r_i$ tends to a constant in $(0, \infty)$.

**Theorem.** As $i \to \infty$ (for $N$ large),
1. non-balanced: $p_i \sim \Gamma(i+1)^{s}\,\theta^{i}\, i^{a}$ (hyper-exponential growth or decay);
2. first-order balanced: $p_i \sim \theta^{i}\, i^{a}$;
3. second-order balanced: $p_i \sim i^{a}$;
4. high-order balanced: $p_i \sim 1$.

The source's Theorem 1(i) and its proof write $\Gamma(i)^{s}$, an off-by-one misprint: for $\chi(i) = i$ the product is $f_i = f_1\, i!$, whose ratio to $\Gamma(i)$ is $i \to \infty$.

**Corollary.** The equilibrium frequencies have power-law asymptotics if and only if the BDIM is second-order balanced, i.e. per-family duplication and loss rates agree to first order and differ at order $1/i$. A first-order balanced model with $\theta < 1$ gives a Pascal (negative binomial) tail with parameters $(a+1, \theta)$ if $a > -1$, and the truncated logarithmic law if $a = -1$.

**Linear BDIM.** For $\lambda_i = \lambda(i + a)$ and $\delta_i = \delta(i + b)$ with $\theta = \lambda/\delta$,

$$f_i = c\,\frac{\nu}{\delta}\,\theta^{i-1}\,\frac{\Gamma(i + a)}{\Gamma(i + 1 + b)}, \qquad c = \frac{\Gamma(1+b)}{\Gamma(1+a)},$$

so $p_i \sim \theta^{i} i^{a - b - 1}$; when $\lambda = \delta$ (second-order balanced) the family-size distribution is a generalized Pareto law with tail exponent $a - b - 1$, steeper than $-1$ exactly when $a < b$ (loss per member falls faster with family size than duplication).

## Depends on

- [Equilibrium of the birth, death and innovation model](equilibrium-of-the-birth-death-and-innovation-model.md)

## Expansion

From the equilibrium formula, $f_i = f_1 \prod_{j=2}^{i} \chi(j)$, so the asymptotics are those of a product. Taking logarithms, $\sum_{j \le i} \log \chi(j) = s \log i! + i \log\theta + a \sum_{j \le i} 1/j + O(1) = s \log \Gamma(i+1) + i\log\theta + a\log i + O(1)$, because $\sum_j O(1/j^2)$ converges; the four cases read off which terms survive. Normalizing by $F_{\mathrm{eq}}$ does not change the $\sim$ class. For the linear model $\chi(j) = \theta (j - 1 + a)/(j + b)$, whose product is a ratio of Gamma functions, and $\Gamma(i+a)/\Gamma(i+1+b) \sim i^{a-b-1}$ by Stirling. Fits of the second-order balanced linear BDIM to domain-family counts in ten genomes gave $0 < a < b$, i.e. tail exponents below $-1$.

## Sources

- G. P. Karev, Y. I. Wolf, A. Y. Rzhetsky, F. S. Berezovskaya and E. V. Koonin, "Birth and death of protein domains: a simple model of evolution explains power law behavior", BMC Evolutionary Biology 2 (2002) 18, Eqs. (3.9)–(3.12), Theorem 1 and Corollaries 1–3, Eqs. (5.7)–(5.10), <https://doi.org/10.1186/1471-2148-2-18>, PMCID PMC137606.
