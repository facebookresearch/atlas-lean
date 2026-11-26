# Bounds on the Shannon index in terms of the maximal frequency

Let $I \ge 2$ be a natural number and let $p = (p_1, \dots, p_I)$ be a probability vector: real numbers $p_i \ge 0$ with $\sum_i p_i = 1$, at least two of them non-zero. Let $M = \max_i p_i$ and let $S = -\sum_i p_i \log p_i$ be the Shannon index, with $0 \log 0 = 0$. Then

$$S_{\min}(M) \le S \le S_{\max}(I, M),$$

where, with $f = \lfloor 1/M \rfloor$,

$$S_{\min}(M) = fM \log \frac{1}{M} + (1 - fM) \log \frac{1}{1 - fM}, \qquad S_{\max}(I, M) = M \log \frac{1}{M} + (1 - M) \log \frac{I - 1}{1 - M},$$

and $\log 0 = 0$.

## Sources

- Bradley K. Moon and Noah A. Rosenberg, "Integer Sequences for Diversity Statistics", Journal of Integer Sequences 29 (2026), Article 26.1.5, Proposition 2 (quoting Aw and Rosenberg, Corollary 3.16).
