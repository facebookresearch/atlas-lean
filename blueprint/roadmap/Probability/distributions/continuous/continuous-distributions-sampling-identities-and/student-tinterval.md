# Student-t interval from the first n observations

For real observations $X_0(\omega), \dots, X_{n-1}(\omega)$ (the first $n$ terms of a sequence) with sample mean $\bar{X}_n(\omega)$, [sample standard deviation](../../../../Chemistry/analytical-chemistry/statistical-treatment-of-analytical-data/sample-std-dev.md) $s_n(\omega)$ (with denominator $n - 1$, and $s_n = 0$ for $n \le 1$), and a real number $q$, the Student-t interval is the closed interval

$$I_n(\omega) = \Bigl[ \bar{X}_n(\omega) - \frac{q\, s_n(\omega)}{\sqrt{n}},\ \bar{X}_n(\omega) + \frac{q\, s_n(\omega)}{\sqrt{n}} \Bigr].$$

With $q = t_{n-1, 1-\alpha/2}$ it is the usual Student-t interval for the mean; the definition itself makes no coverage claim.

With the conventions $x / 0 = 0$ and an empty sample mean of $0$, at $n = 0$ the interval is $\{0\}$.
