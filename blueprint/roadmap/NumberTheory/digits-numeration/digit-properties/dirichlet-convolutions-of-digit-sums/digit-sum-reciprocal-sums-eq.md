# Exact formulas for the reciprocal digit sums

Let $q \ge 2$ be an integer and let $s_q(n)$
denote the sum of the base-$q$ digits of $n$. Let $F$ be the Trollope–Delange fluctuation and $J$
the remainder of the Trollope–Delange formula in base $q$, and for real $x$ put
$G(x) = \int_1^x F(\log u / \log q) \, du / u$, $H(x) = \int_1^x G(u) \, du / u$,
$K(x) = \int_1^x J(u) \, du / u^2$ and $L(x) = \int_1^x K(u) \, du / u$. Then for every real
number $x \ge 1$,

$$\sum_{n=1}^{\lfloor x \rfloor} \frac{s_q(n)}{n} = \frac{(q - 1) \log^2 x}{4 \log q} +
\frac{(q - 1) \log x}{2 \log q} + F\left(\frac{\log x}{\log q}\right) + G(x) + \frac{J(x)}{x} +
K(x)$$

and

$$\sum_{n=1}^{\lfloor x \rfloor} \frac{s_q(n) \log n}{n} = \frac{(q - 1) \log^3 x}{6 \log q} +
\frac{(q - 1) \log^2 x}{4 \log q} + \log x \cdot F\left(\frac{\log x}{\log q}\right) +
(\log x - 1) \, G(x) - H(x) + \frac{J(x) \log x}{x} + (\log x - 1) \, K(x) - L(x).$$

## Sources

- Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43, Lemma 1, equations (4) and (5).
