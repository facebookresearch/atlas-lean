# Dense sequences contain long divisibility chains

For every strictly increasing sequence $a_0 < a_1 < \cdots$ of integers with $a_0 \ge 2$ and positive lower logarithmic density (there is $\delta > 0$ with $\sum_{i < x,\, a_i \le x} 1/a_i \ge \delta \log x$ for all sufficiently large integers $x$), there is a strictly increasing sequence of indices $n_0 < n_1 < \cdots$ with $a_{n_i} \mid a_{n_{i+1}}$ for every $i$ such that

$$\limsup_{x \to \infty} \frac{\#\{i < x : a_{n_i} < x\}}{\log\log x} \ge \limsup_{x \to \infty} \frac{1}{\log \log x} \sum_{i < x,\ a_i < x} \frac{1}{a_i \log a_i},$$

the limits superior taken over integers $x$ in the extended reals.

## Sources

- T. F. Bloom, Erdős Problems, Problem #1217, https://www.erdosproblems.com/1217.
- B. Alexeev, K. Barreto, Y. Li, J. D. Lichtman, L. Price, J. I. Shah, Q. Tang and T. Tao, Primitive sets and von Mangoldt chains: Erdős Problem #1196 and beyond, arXiv:2605.00301 (2026), Theorem 1.6.
