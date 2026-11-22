# Enflo type

Let $X$ be a real normed space, $C \in [0, \infty]$ and $p$ a real number. We
say that $X$ has Enflo type $p$ with constant $C$ if for every $n \ge 1$ and every function
$f : \{-1, 1\}^n \to X$,

$$
\mathbb{E}\Bigl\|\frac{f(\varepsilon) - f(-\varepsilon)}{2}\Bigr\|^p \le
C^p \sum_{j=1}^n \mathbb{E}\,\|D_j f(\varepsilon)\|^p,
$$

where $\varepsilon = (\varepsilon_1, \dots, \varepsilon_n)$ is a sequence of independent
Rademacher random variables, $-\varepsilon = (-\varepsilon_1, \dots, -\varepsilon_n)$, and
$D_j f$ is the discrete partial derivative of $f$ in direction $j$. Both sides are computed in $[0, \infty]$, with $a^0 = 1$ for every $a$ (so $0^0 = \infty^0 = 1$), $0^p = 0$ and
$\infty^p = \infty$ for $p > 0$, $0^p = \infty$ and $\infty^p = 0$ for $p < 0$, and $0 \cdot \infty = 0$.
