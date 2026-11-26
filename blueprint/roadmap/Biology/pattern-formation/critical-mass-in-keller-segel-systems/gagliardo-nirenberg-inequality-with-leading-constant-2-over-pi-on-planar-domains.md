# Gagliardo–Nirenberg inequality with leading constant $2/\pi$ on planar domains

**Setting.** Let $\Omega \subset \mathbb{R}^2$ be a bounded domain with smooth boundary. On the whole plane, the sharp Gagliardo–Nirenberg–Sobolev inequality reads $\pi \int_{\mathbb{R}^2} v^6 \le \left(\int_{\mathbb{R}^2} v^4\right)\left(\int_{\mathbb{R}^2} |\nabla v|^2\right)$ for $v \in W^{1,2}(\mathbb{R}^2)$.

**Relative isoperimetry at small volume.** For every $\varepsilon > 0$ there is $\mathfrak{s} \in (0,|\Omega|]$ such that every finite-perimeter set $E \subset \Omega$ with $|E| \le \mathfrak{s}$ satisfies

$$ \mathscr{P}_\Omega(E)^2 \ge (2\pi - \varepsilon)\,|E|, $$

where $\mathscr{P}_\Omega(E)$ is the perimeter of $E$ relative to $\Omega$ (boundary of $E$ lying on $\partial\Omega$ is not counted). The constant $2\pi$ is half the planar isoperimetric constant $4\pi$: the worst small sets are half-discs sitting on a smooth boundary.

**Theorem.** For every $\varepsilon > 0$ there is $C > 0$ such that

$$ \int_\Omega f^6 \le \left(\frac{2}{\pi} + \varepsilon\right)\left(\int_\Omega f^4\right)\left(\int_\Omega |\nabla f|^2\right) + C\left(\int_\Omega f^4\right)^{3/2} $$

for all nonnegative $f \in C^1(\overline\Omega)$.

The leading constant $2/\pi$ is twice the whole-plane constant $1/\pi$, mirroring the halving of the isoperimetric constant at the boundary.

## Expansion

Truncate $f$ at the level whose superlevel set has measure $\mathfrak{s}$, so the high part $g$ lives on small sets. Its decreasing rearrangement $g^*$ on $(0,S)$, $S \le \mathfrak{s}$, satisfies $\int_0^S s|(g^*)'(s)|^2\,ds \le a^{-1}\int_\Omega|\nabla g|^2$ for any $a < 2\pi$, by the coarea formula and the relative isoperimetric inequality applied to level sets. Building the radial Schwarz symmetrization $G$ on a disc from $g^*$ converts this into $\int|\nabla G|^2 \le (4\pi/a)\int|\nabla g|^2$ while preserving all $L^p$ norms; applying the sharp planar inequality to $G$ and letting $a \uparrow 2\pi$ gives the constant $2/\pi$. The low part is bounded and contributes the $(\int f^4)^{3/2}$ remainder. In the Keller–Segel application this constant converts into the subcritical mass condition $m < 4\pi$.

## Sources

- Lili Du, Yulan Wang and Yichen Zhang, "On the optimal mass threshold for the two-dimensional Keller-Segel system coupled to the Navier-Stokes equations", arXiv:2611.09160 (2026), Section 2.2, Lemmas 2.3, 2.4 and 2.5, <https://doi.org/10.48550/arXiv.2611.09160>.
