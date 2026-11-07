# Mean ergodic theorem for bilinear polynomial averages

Let $(X, \mu)$ be a $\sigma$-finite
measure space and let $T : X \to X$ be a measurable bijection with measurable inverse that
preserves $\mu$. Let $P \in \mathbb{Z}[t]$ have degree at least $2$, and let
$p_1, p_2 \in (1, \infty)$ and $p \in [0, \infty]$ satisfy $p_1^{-1} + p_2^{-1} = p^{-1}$ and
$p^{-1} \le 1$. For a real number $N \ge 0$, functions $f, g : X \to \mathbb{C}$ and $x \in X$ let

$$A_N(f, g)(x) = \frac{1}{\lfloor N \rfloor}
\sum_{n=1}^{\lfloor N \rfloor} f(T^n x)\, g(T^{P(n)} x),$$

with $A_N(f, g)(x) = 0$ when $\lfloor N \rfloor = 0$, where $T^k$ for $k \in \mathbb{Z}$ is the
$k$-th power of $T$ in the group of bijections of $X$. Then for all
$f \in L^{p_1}(\mu)$ and $g \in L^{p_2}(\mu)$ with values in $\mathbb{C}$ there is a function
$h : X \to \mathbb{C}$ in $L^p(\mu)$ such that $\|A_N(f, g) - h\|_{L^p(\mu)} \to 0$ as the real
number $N$ tends to $\infty$.

This is Theorem 1.17(i) of Krause, Mirek and Tao.

## Sources

- B. Krause, M. Mirek, and T. Tao, `Pointwise ergodic theorems for non-conventional bilinear polynomial averages`, Annals of Math, 195 (3) 2022. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2022-195-3-PointwiseErgodicTheorems.lean Via leanprover/lean-eval@38361be, problem `annals_pointwise_ergodic_theorems`.
