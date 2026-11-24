# Integrating against a Radon–Nikodym derivative

Let $\mu$ and $\nu$ be measures on a measurable space $\Omega$ such that $\mu$ has a Lebesgue decomposition with
respect to $\nu$ and $\mu$ is absolutely continuous with respect to $\nu$. Let
$\frac{d\mu}{d\nu} \colon \Omega \to [0, \infty]$ be the Radon–Nikodym derivative of $\mu$ with respect to $\nu$, the
density $f$ of a chosen Lebesgue decomposition $\mu = \xi + f \cdot \nu$ with $\xi$ singular with respect to $\nu$.
Then for every function $g \colon \Omega \to [0, \infty]$ that is $\nu$-almost everywhere measurable,

$$
\int_\Omega \frac{d\mu}{d\nu} \, g \, d\nu = \int_\Omega g \, d\mu,
$$

where the integrals are integrals of functions with values in $[0, \infty]$ and $0 \cdot \infty = 0$.
