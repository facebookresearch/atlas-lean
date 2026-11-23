# Drift of gamete frequencies matches recombination

Let $x$ be a vector of four gamete frequencies with $\sum_g x_g = 1$, let $N$, $r$ and $\rho$ be real numbers with $\rho = 4Nr$, and let $g$ be a gamete. Then the [two-locus generator](two-locus-generator.md) without mutation, applied to the coordinate $x_g$ and evaluated at $x$, is

$$L_{\rho,0}\, x_g = 2N\bigl((1 - r)\, x_g + r\, p_{g_1} q_{g_2} - x_g\bigr),$$

When $x$ is a vector of nonnegative frequencies and $0 \le r \le 1$, this is $2N$ times the change of the frequency of $g$ in one generation of random mating with recombination fraction $r$, where $p_{g_1}$ is the frequency of the first-locus allele of $g$ and $q_{g_2}$ that of its second-locus allele.
