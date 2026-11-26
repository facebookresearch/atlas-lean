# Set integrals of the path expectation

Let $\mu$ be a probability measure on $\Omega$, let
$(\mathcal{F}_t)_{t \ge 0}$ be a filtration of the σ-algebra of $\Omega$ indexed by
$\mathbb{R}_{\ge 0}$, and let $(B_t)_{t \ge 0}$ be a real process such that each $B_t$ is
$\mathcal{F}_t$-measurable and, for all $u \le t$, the increment $B_t - B_u$ is independent of
$\mathcal{F}_u$ under $\mu$. Let $s \ge 0$, let $Y$ be a measurable real function on paths
$\mathbb{R}_{\ge 0} \to \mathbb{R}$ with $|Y(p)| \le C$ for every path $p$, and let
$A \in \mathcal{F}_s$. Write $\nu_s$ for the law under $\mu$ of
$\omega \mapsto (t \mapsto B_{s+t}(\omega) - B_s(\omega))$,
$E_s Y(x) = \int Y(t \mapsto x + f(t))\, d\nu_s(f)$ for $x \in \mathbb{R}$, and
$\theta_s \omega$ for the shifted path $t \mapsto B_{s+t}(\omega)$. Then

$$
\int_A E_s Y(B_s(\omega))\, d\mu(\omega)
  = \int_A Y^+(\theta_s \omega)\, d\mu(\omega) - \int_A Y^-(\theta_s \omega)\, d\mu(\omega),
$$

where $Y^+ = \max(Y, 0)$, $Y^- = \max(-Y, 0)$, and each integral on the right is the integral of
a nonnegative function, taken in $[0, \infty]$ and then converted to a real number.
