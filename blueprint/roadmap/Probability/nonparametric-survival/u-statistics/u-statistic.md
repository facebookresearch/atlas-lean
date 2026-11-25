# U-statistic

Let $\alpha$ be a set, $h : \alpha^m \to \mathbb{R}$ a kernel of degree $m$ and $x = (x_1, \dots, x_n) \in \alpha^n$ a sample of size $n$. The U-statistic is the average of $h(x_{f(1)}, \dots, x_{f(m)})$ over the $n(n-1)\cdots(n - m + 1)$ injective maps $f : \{1, \dots, m\} \to \{1, \dots, n\}$:

$$U(h; x) = \frac{1}{n(n-1)\cdots(n - m + 1)} \sum_{f \text{ injective}} h(x_{f(1)}, \dots, x_{f(m)}).$$

For $m > n$ there are no such maps and the value is $0$ by convention.

## Sources

- Wassily Hoeffding, *A class of statistics with asymptotically normal distribution*, Ann. Math. Statist. 19 (1948), no. 3, 293–325, DOI 10.1214/aoms/1177730196.
