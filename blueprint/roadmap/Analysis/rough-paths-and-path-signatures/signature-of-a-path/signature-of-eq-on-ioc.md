# Signature of a linear segment is the exponential of its increment

Let $s \le t$ and $x \in \mathbb{R}^\iota$, and suppose the velocity of $X$ equals $x$ on
$(s, t]$, so that $X$ is linear on $[s, t]$ with increment $X_t - X_s = (t - s)\,x$. Then

$$S(X)_{s,t} = \exp\big((t-s)\,x\big) = \sum_{k \ge 0} \frac{\big((t-s)\,x\big)^{\otimes k}}{k!},$$

that is, $S(X)^{i_1 \cdots i_k}_{s,t} = (t - s)^k\, x_{i_1} \cdots x_{i_k} / k!$ for every word.
In particular the coefficient depends only on how many times each letter occurs in the word.

## Sources

- I. Chevyrev and A. Kormilitzin, *A primer on the signature method in machine learning*,
  arXiv:1603.03788v2, Example 1.20 and equation (17).
