# Double half cousins with inbred founders realize every admissible IBD point

For noninbred $a, b$ let $\kappa = (\kappa_0, \kappa_1, \kappa_2)$ be the probabilities that they share $0$, $1$ or $2$ alleles IBD at a locus. Thompson's inequality $\kappa_1^2 \ge 4\kappa_0\kappa_2$ holds for every relationship between noninbred individuals; a point $(\kappa_0, \kappa_2)$ of the IBD triangle $\{\kappa_0, \kappa_2 \ge 0, \kappa_0 + \kappa_2 \le 1\}$ satisfying it is called admissible.

Double half cousins $\mathrm{DHC}^{f_1, f_2}_{m,n}$ are two individuals whose fathers are half cousins with separation $m$ and founder inbreeding $f_1$, whose mothers are half cousins with separation $n$ and founder inbreeding $f_2$, with no other relationships (Definition 6). If the fathers have kinship $\phi_1$, the mothers kinship $\phi_2$, and fathers are unrelated to mothers, then $a, b$ are noninbred and

$$\kappa_0 = (1 - \phi_1)(1 - \phi_2), \qquad \kappa_2 = \phi_1 \phi_2. \tag{9}$$

**Theorem** (Theorems 7 and 8 of the source). Every admissible point is the IBD coefficient vector of a double-half-cousin relationship with inbred founders, and hence, when inbred founders are allowed, of a relationship in a finite pedigree. Explicitly, with $U = 1 + \kappa_2 - \kappa_0$ and $D = U^2 - 4\kappa_2 = \kappa_1^2 - 4\kappa_0\kappa_2$, take $\phi_{1,2} = \tfrac12(U \mp \sqrt D)$, which satisfy $0 \le \phi_1 \le \phi_2 \le 1$, and realize each $\phi_j$ by half cousins as in Theorem 2, giving $m = \lfloor \log_2(2/(U - \sqrt D)) \rfloor$, $n = \lfloor \log_2(2/(U + \sqrt D)) \rfloor$, $f_1 = 2^m(U - \sqrt D) - 1$, $f_2 = 2^n(U + \sqrt D) - 1$ when $0 < \phi_1, \phi_2 < 1$ (Eq. (11)).

## Depends on

- [Every kinship coefficient is realized by half cousins with an inbred founder](half-cousin-kinship-with-inbred-founder.md)

## Proof depends on

- [Every kinship coefficient is realized by half cousins with an inbred founder](half-cousin-kinship-with-inbred-founder.md)

## Expansion

Equation (9): the paternal alleles of $a$ and $b$ are random alleles of the two fathers, IBD with probability $\phi_1$, independently of the maternal pair. Then $\phi_1 + \phi_2 = U$ and $\phi_1\phi_2 = \kappa_2$, so $\phi_1, \phi_2$ are the roots of $\phi^2 - U\phi + \kappa_2 = 0$; the discriminant $U^2 - 4\kappa_2$ equals $\kappa_1^2 - 4\kappa_0\kappa_2$, which is nonnegative exactly when $\kappa$ is admissible. Edge cases: $\phi_j = 1$ uses separation $0$ with inbreeding $1$, and $\kappa_2 = 0$ gives $m = \infty$, which collapses to ordinary half cousins on the maternal side; $\kappa = (1, 0, 0)$ is any pair of noninbred founders. This replaces Karigl's construction, which needed up to four infinite pedigree parts (Section 5.2).

## Sources

- M. D. Vigeland, Relatedness coefficients in pedigrees with inbred founders, Journal of Mathematical Biology 81 (2020), 185-207. <https://doi.org/10.1007/s00285-020-01505-x> (PMCID PMC7363742)
