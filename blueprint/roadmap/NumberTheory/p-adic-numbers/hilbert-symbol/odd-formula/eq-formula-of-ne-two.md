# Formula for the $p$-adic Hilbert symbol at an odd prime

Let $p$ be an odd prime and let
$a, b \in \mathbb{Q}_p$ be nonzero. Write $a = p^\alpha u$ and $b = p^\beta v$ with
$\alpha, \beta \in \mathbb{Z}$ and $u, v$ units of $\mathbb{Z}_p$, and let $\bar u, \bar v$ be the
residues of $u, v$ modulo $p$. Then the $p$-adic Hilbert symbol satisfies

$$(a, b)_p = (-1)^{\alpha \beta \varepsilon(p)} \left(\frac{\bar u}{p}\right)^{\beta}
  \left(\frac{\bar v}{p}\right)^{\alpha},$$

where $\varepsilon(p)$ is the class of $(p - 1)/2$ modulo $2$ and $\left(\frac{\cdot}{p}\right)$
is the Legendre symbol.
As these signs are $\pm 1$, the exponents $\alpha \beta \varepsilon(p)$, $\beta$ and $\alpha$ are
taken in absolute value, and the Legendre symbol of a residue is evaluated at its representative
in $\{0, \dots, p - 1\}$.

## Sources

- J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973, Chapter III, §1.2, Theorem 1, p. 20 (the case $p \neq 2$). Serre defines $(a, b) = 1$ by a nonzero zero of $z^2 - a x^2 - b y^2$; this agrees with the definition used here by `hilbertSymbol.eq_one_iff_exists_ternary_eq_zero`.
