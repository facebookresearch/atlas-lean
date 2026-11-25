# Pointwise ergodic theorem for bilinear polynomial averages

Let $(X, \mu)$ be a $\sigma$-finite
measure space and let $T : X \to X$ be a measurable bijection with measurable inverse that
preserves $\mu$. Let $P \in \mathbb{Z}[t]$ have degree at least $2$, and let
$p_1, p_2 \in (1, \infty)$ and $p \in [0, \infty]$ satisfy $p_1^{-1} + p_2^{-1} = p^{-1}$ and
$p^{-1} \le 1$. For a real number $N \ge 0$, functions $f, g : X \to \mathbb{C}$ and $x \in X$ let

$$A_N(f, g)(x) = \frac{1}{\lfloor N \rfloor}
\sum_{n=1}^{\lfloor N \rfloor} f(T^n x)\, g(T^{P(n)} x),$$

with $A_N(f, g)(x) = 0$ when $\lfloor N \rfloor = 0$, where $T^k$ for $k \in \mathbb{Z}$ is the
$k$-th power of $T$ in the group of bijections of $X$. Then for
all $f \in L^{p_1}(\mu)$ and $g \in L^{p_2}(\mu)$ with values in $\mathbb{C}$ there is a function
$h : X \to \mathbb{C}$ in $L^p(\mu)$ such that for $\mu$-almost every $x \in X$,
$A_N(f, g)(x) \to h(x)$ as the real number $N$ tends to $\infty$.

This is Theorem 1.17(ii) of Krause, Mirek and Tao.

## Sources

- Ben Krause, Mariusz Mirek and Terence Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
  averages*, Ann. of Math. (2) 195 (2022), no. 3, 997–1109, DOI 10.4007/annals.2022.195.3.4, Theorem 1.17(ii);
  arXiv:2008.00857.
- Annals Challenge (Imperial College London), <https://github.com/ImperialCollegeLondon/AnnalsChallenge>; problem
  `annals_pointwise_ergodic_theorems` of the lean-eval benchmark.
