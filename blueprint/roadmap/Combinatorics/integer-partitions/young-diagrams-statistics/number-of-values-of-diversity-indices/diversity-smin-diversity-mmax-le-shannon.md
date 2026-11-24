# Bounds on the Shannon index in terms of the Gini–Simpson index

Let $I \ge 2$ be a natural number and let $p = (p_1, \dots, p_I)$ be a probability vector: real numbers $p_i \ge 0$ with $\sum_i p_i = 1$, at least two of them non-zero. Let $J = \sum_i p_i^2$, so that the Gini–Simpson index is $H = 1 - J$, and let $S = -\sum_i p_i \log p_i$ be the Shannon index, with $0 \log 0 = 0$. Then

$$S_{\min}\big(M_{\max}(I, J)\big) \le S \le S_{\max}\big(I, M_{\min}(J)\big),$$

where $M_{\min}(J) = \frac{1}{c}\left(1 + \sqrt{(cJ - 1)/(c - 1)}\right)$ with $c = \lceil 1/J \rceil$, $M_{\max}(I, J) = \frac{1}{I}\left(1 + \sqrt{(IJ - 1)(I - 1)}\right)$, $S_{\min}(M) = fM \log(1/M) + (1 - fM)\log(1/(1 - fM))$ with $f = \lfloor 1/M \rfloor$, $S_{\max}(I, M) = M \log(1/M) + (1 - M) \log((I - 1)/(1 - M))$, and $\log 0 = 0$. The source's hypothesis $0 < H \le 1 - 1/I$ holds for every such $p$.

## Sources

- Bradley K. Moon and Noah A. Rosenberg, "Integer Sequences for Diversity Statistics", Journal of Integer Sequences 29 (2026), Article 26.1.5, Theorem 3.
