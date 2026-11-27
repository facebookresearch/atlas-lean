# Bias correction, variance and asymptotic normality of the FracMinHash containment estimator

**Setting.** Let $h$ be a hash function onto $[0,H]$, modelled as uniformly random, and $0 < s < 1$ a scale factor. The FracMinHash sketch of a finite set $A$ is

$$\mathrm{FRAC}_s(A) = \{\, h(a) : a \in A,\ h(a) \le Hs \,\},$$

so $X_A := |\mathrm{FRAC}_s(A)| \sim \mathrm{Binomial}(|A|, s)$. The containment index of $A$ in $B$ is $C(A,B) = |A \cap B|/|A|$ and its naive sketch estimate is $\hat C_{\mathrm{frac}}(A,B) = |\mathrm{FRAC}_s(A) \cap \mathrm{FRAC}_s(B)| / |\mathrm{FRAC}_s(A)|$. Write $n = |A \cap B|$ and $m = |A \setminus B|$, both assumed nonzero; then $X_{A\cap B} \sim \mathrm{Bin}(n,s)$ and $X_{A\setminus B} \sim \mathrm{Bin}(m,s)$ are independent.

**Theorem 1 (bias).** $\ \mathbb{E}\big[\hat C_{\mathrm{frac}}(A,B)\,\mathbb{1}\{X_A > 0\}\big] = \dfrac{|A\cap B|}{|A|}\big(1 - (1-s)^{|A|}\big).$

**Theorem 2 (debiased estimator).** The fractional containment index

$$C_{\mathrm{frac}}(A,B) = \frac{|\mathrm{FRAC}_s(A)\cap \mathrm{FRAC}_s(B)|}{|\mathrm{FRAC}_s(A)|\,\big(1-(1-s)^{|A|}\big)}\,\mathbb{1}\{X_A > 0\}$$

satisfies $\mathbb{E}[C_{\mathrm{frac}}(A,B)] = C(A,B)$.

**Theorem 3 and Corollary 1 (variance).** To first order in a Taylor expansion,

$$\operatorname{Var}[\hat C_{\mathrm{frac}}(A,B)] \approx \frac{mn(1-s)}{s(m+n)^3},\qquad \operatorname{Var}[C_{\mathrm{frac}}(A,B)] \approx \frac{mn(1-s)}{s(m+n)^3\big(1-(1-s)^{|A|}\big)^2}.$$

**Theorem 4 (asymptotic normality).** With $g(x,y) = x/(x+y)$, let $n, m \to \infty$ with $n/(n+m) \to c \in (0,1)$. Then

$$\sqrt{n+m}\,\big(g(X_{A\cap B}, X_{A\setminus B}) - g(n,m)\big) \xrightarrow{\ D\ } \mathcal{N}\!\left(0,\ \frac{c(1-c)(1-s)}{s}\right).$$

Equivalently, $g(X_{A\cap B}, X_{A\setminus B})$ is approximately $\mathcal{N}\big(g(n,m),\ mn(1-s)/(s(m+n)^3)\big)$. The source displays the limit with the unscaled variance $mn(1-s)/((m+n)^3 s)$ on the right; that variance tends to $0$, so the page states the limit with the rescaled variance, as Theorem 3 gives it.

## Expansion

The naive estimator equals $X_{A\cap B}/(X_{A\cap B}+X_{A\setminus B})$. Conditioning on $X_A = k > 0$, the $k$ sketched elements of $A$ form a uniform $k$-subset of $A$, so the conditional mean of the ratio is $n/(n+m)$; multiplying by $\Pr(X_A > 0) = 1-(1-s)^{|A|}$ gives Theorem 1, and dividing it out gives Theorem 2. The variance and normality results apply the delta method to $g$ at $(sn, sm)$ using the binomial means and variances and the De Moivre–Laplace theorem. For large $|A|$ and moderate $s$ the bias factor is essentially $1$, which is why the naive estimate only misbehaves on short sequences such as viral genomes.

## Sources

- Rahman Hera M, Pierce-Ward NT, Koslicki D, "Deriving confidence intervals for mutation rates across a wide range of evolutionary distances using FracMinHash", Genome Res (2023), Theorems 1–4 and Corollary 1, Eqs. (1)–(4), <https://doi.org/10.1101/gr.277651.123>, PMCID PMC10538494.
