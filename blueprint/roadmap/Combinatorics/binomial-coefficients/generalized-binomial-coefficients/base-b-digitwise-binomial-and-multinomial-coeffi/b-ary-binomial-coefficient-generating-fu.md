# Generating function of the $b$-ary binomial coefficients

Let $R$ be a commutative semiring,
let $x \in R$, let $b \ge 2$, and write $\binom{n}{k}_b$ for the $b$-ary binomial coefficient of
natural numbers $n$ and $k$. Let $n$ have base-$b$ digits $n_0, \dots, n_{m-1}$, where $m$ is
the number of base-$b$ digits of $n$ ($m = 0$ for $n = 0$). Then

$$
\sum_{k=0}^{n} \binom{n}{k}_b x^k = \prod_{l=0}^{m-1} \left(1 + x^{b^l}\right)^{n_l}.
$$

## Sources

- Lin Jiu and Christophe Vignat, *On Binomial Identities in Arbitrary Bases*, J. Integer Seq. 19 (2016), Article 16.5.5, Theorem 6 (equation (13)), <https://cs.uwaterloo.ca/journals/JIS/VOL19/Jiu/jiu3.html>.
