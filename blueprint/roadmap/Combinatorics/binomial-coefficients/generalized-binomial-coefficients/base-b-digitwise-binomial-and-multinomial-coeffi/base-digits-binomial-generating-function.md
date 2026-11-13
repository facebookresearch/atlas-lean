# Generating function of digitwise binomial products

Let $R$ be a commutative ring, let
$x \in R$, let $b \ge 2$, and let $n$ have base-$b$ digits $n_0, \dots, n_{m-1}$, where $m$ is
the number of base-$b$ digits of $n$ ($m = 0$ for $n = 0$). For each natural number $k$ let
$k_l$ be its $l$-th base-$b$ digit, taken to be $0$ beyond the last digit. Then

$$
\sum_{k=0}^{n} \Bigl(\prod_{l=0}^{m-1} \binom{n_l}{k_l}\Bigr) x^k
= \prod_{l=0}^{m-1} \left(1 + x^{b^l}\right)^{n_l}.
$$

The product $\prod_{l=0}^{m-1} \binom{n_l}{k_l}$ is the $b$-ary binomial coefficient of $n$
and $k$ whenever $k \le n$.

## Sources

- Lin Jiu and Christophe Vignat, "On Binomial Identities in Arbitrary Bases," Journal of Integer Sequences 19 (2016), Article 16.5.5, Theorem (equation eq:barybinomialgeneratingfunction), lines 322–329, https://cs.uwaterloo.ca/journals/JIS/VOL19/Jiu/jiu4.tex
