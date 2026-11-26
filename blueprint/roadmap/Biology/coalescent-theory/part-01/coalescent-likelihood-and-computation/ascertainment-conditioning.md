# Ascertainment conditioning in site-frequency likelihoods

When single-nucleotide polymorphisms are first discovered in a panel and then typed in a larger sample, only sites that meet the discovery condition enter the data, so the observed spectrum is a conditional one. Nielsen, Hubisz and Clark (2004) write the likelihood of the unascertained spectrum $P = (p_1, \dots, p_{n-1})$, for independent loci, as the product over loci of $\Pr(X_i = x_i \mid P)\Pr(\mathrm{Asc}_i \mid X_i = x_i)/\Pr(\mathrm{Asc}_i \mid P)$ (their Equation 1). In their basic case the discovery panel is a subset of fixed depth $d$, $2 \le d \le n$, of the final sample of size $n$, and a site is ascertained if it is variable in the panel. The formula below treats the panel as $d$ of the $n$ copies drawn uniformly at random without replacement (equivalently, the allelic types are exchangeable over the $n$ sample positions given the full-sample count $x$), so that the number of derived copies in the panel is hypergeometric given $x$. A subset of fixed size alone is not enough: for four labelled copies with types $(1, 1, 0, 0)$ and a panel consisting of the first two, the site is never variable in the panel, whereas the formula gives $2/3$. Under this protocol a site with $x$ derived copies is ascertained with probability one minus the probability that all $d$ panel copies come from the $x$ derived or from the $n - x$ ancestral copies,

$$a(x) = 1 - \frac{\binom{x}{d} + \binom{n-x}{d}}{\binom{n}{d}},$$

with $\binom{j}{d} = 0$ for $j < d$ (Equation 2). For $2 \le d \le n$ every $a(x)$, $1 \le x \le n - 1$, is positive, since some panel contains one derived and one ancestral copy; at $d = 1$ every $a(x)$ is zero, no site is ascertained and there is no conditional spectrum. With all $a(x) > 0$, the ascertained derived counts have law $p_x a(x)/\sum_y p_y a(y)$, and maximizing $\sum_x n_x\log\bigl(p_x a(x)/\sum_y p_y a(y)\bigr)$ over the simplex gives $\hat p_x \propto n_x/a(x)$, where $n_x$ is the number of observed loci with frequency $x$ (their Equation 3). They extend the likelihood to a frequency cutoff in discovery, to depths that vary among loci with known or unknown values, and to further discovery protocols, and show by simulation that with $d = 5$ and $n = 20$ the ascertained spectrum has a marked excess of intermediate frequencies that the correction removes.

## Expansion

1. The ascertainment-conditioned likelihood for independent loci (Equation 1).
2. The ascertainment probability for a discovery panel of depth $2 \le d \le n$ drawn uniformly without replacement from the sample, or with types exchangeable over positions given $x$ (Equation 2), and its versions with a frequency cutoff and with variable depth.
3. The maximum-likelihood reconstitution of the spectrum and its closed form $\hat p_x \propto n_x/a(x)$, which requires $a(x) > 0$ for every $x$.
4. Use of the corrected spectrum or of the conditioned likelihood in demographic inference, and the bias when ascertainment is ignored.

## Sources

- R. Nielsen, M. J. Hubisz and A. G. Clark, Reconstituting the frequency spectrum of ascertained single-nucleotide polymorphism data, Genetics 168 (2004), 2373–2382, Equations 1–5 (basic case: Equations 1–3) and Figure 1. <https://doi.org/10.1534/genetics.104.031039>
