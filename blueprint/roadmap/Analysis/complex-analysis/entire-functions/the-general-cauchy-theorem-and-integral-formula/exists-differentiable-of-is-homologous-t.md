# Claim 2 in the proof of Cauchy's integral formula: `h` is holomorphic

Let $\Omega \subseteq \mathbb{C}$ be open, let $f$ be holomorphic on $\Omega$, and let $\gamma$ be a closed piecewise $C^1$ path homologous to zero in $\Omega$. Let $g(z, \zeta) = (f(\zeta) - f(z))/(\zeta - z)$ for $\zeta \ne z$ and $g(z, z) = f'(z)$, and let $\Omega' = \{z \notin \gamma : n(\gamma, z) = 0\}$. Then $\Omega \cup \Omega' = \mathbb{C}$, and there is an entire function $h$ with

$$h(z) = \frac{1}{2\pi i} \int_\gamma g(z, \zeta)\, d\zeta \ \ (z \in \Omega), \qquad h(z) = \frac{1}{2\pi i} \int_\gamma \frac{f(\zeta)}{\zeta - z}\, d\zeta \ \ (z \in \Omega').$$
