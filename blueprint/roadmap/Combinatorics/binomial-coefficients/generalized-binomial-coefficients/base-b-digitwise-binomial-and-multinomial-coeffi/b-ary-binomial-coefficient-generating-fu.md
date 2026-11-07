# Generating function of the $b$-ary binomial coefficients

Let $R$ be a commutative semiring,
let $x \in R$, let $b \ge 2$, and write $\binom{n}{k}_b$ for the $b$-ary binomial coefficient of
natural numbers $n$ and $k$. Let $n$ have base-$b$ digits $n_0, \dots, n_{m-1}$, where $m$ is
the number of base-$b$ digits of $n$ ($m = 0$ for $n = 0$). Then

$$
\sum_{k=0}^{n} \binom{n}{k}_b x^k = \prod_{l=0}^{m-1} \left(1 + x^{b^l}\right)^{n_l}.
$$

## Sources

- Lin Jiu and Christophe Vignat, "On Binomial Identities in Arbitrary Bases," Journal of Integer Sequences 19 (2016), Article 16.5.5, Theorem (equation eq:barybinomialgeneratingfunction), lines 322–329, https://cs.uwaterloo.ca/journals/JIS/VOL19/Jiu/jiu4.tex
