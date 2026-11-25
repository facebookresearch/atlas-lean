# Radon–Nikodym theorem for finite signed measures

Let $\mu$ be a σ-finite measure on a set $\alpha$ with a σ-algebra, and let $s$ be a signed measure on $\alpha$: a
countably additive function from the measurable sets to $\mathbb{R}$. Suppose that $s$ is absolutely continuous with
respect to $\mu$: $s(E) = 0$ for every measurable $E$ with $\mu(E) = 0$. Then $s$ is the signed measure with density
$ds/d\mu$ with respect to $\mu$:

$$s(E) = \int_E \frac{ds}{d\mu} \, d\mu \qquad \text{for every measurable } E \subseteq \alpha,$$

where $ds/d\mu$ is integrable, by the card's second statement. (The signed measure with a given density is defined to be
$0$ when the density is not integrable, a convention that plays no role here.) Here
$ds/d\mu \colon \alpha \to \mathbb{R}$ is the Radon–Nikodym derivative of $s$ with respect to $\mu$, the difference of
the Radon–Nikodym derivatives with respect to $\mu$ of the positive and negative parts of the Jordan decomposition of
$s$, with values in $[0, \infty]$ converted to real numbers, $\infty$ to $0$.
