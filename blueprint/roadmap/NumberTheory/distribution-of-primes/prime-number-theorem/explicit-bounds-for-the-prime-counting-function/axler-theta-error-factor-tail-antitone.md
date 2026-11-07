# The last branch of Axler's error factor is nonincreasing

Let $R = 5.5666305$ and for
real $y \ge e^{673}$ let

$$
a(y) = \log^6 y \cdot 121.0961 \Big(\frac{\log y}{R}\Big)^{3/2}
\exp\Big(-2\sqrt{\frac{\log y}{R}}\Big).
$$

Then $a(x) \le a(x_1)$ for all reals $x_1$ and $x$ with $e^{673} \le x_1 \le x$.

This is the paper's function $a$ on $y \ge e^{673}$. The paper prints the statement as
$a_n(x) \le a_n(x_1)$; its proof ($a'(x) < 0$ for $x \ge e^{673}$) and the later use
$a(t) \le a(x_1)$ show that $a_n$ is a typo for $a$.

## Sources

- Christian Axler, *Effective Estimates for Some Functions Defined over Primes*, INTEGERS 24 (2024), Article A34, Lemma 5 (`integers-2024-A34-lem-5`), with the function `a` defined at the start of Section 6.
