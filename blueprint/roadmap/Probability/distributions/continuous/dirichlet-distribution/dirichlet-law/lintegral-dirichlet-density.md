# The Dirichlet integral

Let $\alpha = (\alpha_0, \dots, \alpha_n) \in \mathbb{R}^{n+1}$ with
$\alpha_i > 0$ for every $i$, and let
$\Delta = \{x \in \mathbb{R}^n : x_i > 0 \text{ for all } i \text{ and } \sum_{i=0}^{n-1} x_i < 1\}$
be the open corner simplex. Then

$$\int_{\Delta} \Bigl(\prod_{i=0}^{n-1} x_i^{\alpha_i - 1}\Bigr)
\Bigl(1 - \sum_{i=0}^{n-1} x_i\Bigr)^{\alpha_n - 1} dx =
\frac{\prod_{i=0}^{n} \Gamma(\alpha_i)}{\Gamma\bigl(\sum_{i=0}^{n} \alpha_i\bigr)},$$

where $dx$ is Lebesgue measure. Equivalently, the integral of the unnormalized Dirichlet density
$D_\alpha$ over $\mathbb{R}^n$ equals the multivariate Beta function $B(\alpha)$.
