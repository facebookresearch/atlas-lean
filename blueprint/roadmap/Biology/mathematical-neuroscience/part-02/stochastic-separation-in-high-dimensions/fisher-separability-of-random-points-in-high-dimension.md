# Fisher separability of random points in high dimension

**Definitions.** Let $(\cdot, \cdot)$ be the standard inner product on $\mathbb{R}^n$ and $0 \le \alpha < 1$. A point $x$ is **Fisher-separable** from a finite set $Y$ with threshold $\alpha$ if

$$(x, y) \le \alpha\, (x, x) \quad \text{for all } y \in Y ,$$

i.e. the linear functional $z \mapsto (x, z)$ with threshold $\alpha(x,x)$ separates $x$ from $Y$; for whitened data (mean zero, identity covariance) this is Fisher's linear discriminant. A finite set is Fisher-separable with threshold $\alpha$ if every point is Fisher-separable from the rest. Equivalently, $x$ is not separable from $y$ iff $x$ lies in the ball $\| z - y/(2\alpha) \| < \|y\|/(2\alpha)$.

**Theorem 1 (distributions in the ball).** Let $Y \subset B^n$ (the unit ball) with $|Y| < b^n$, and let a probability density on $B^n$ satisfy $\rho_{\max} < C/(r^n V(B^n))$ for constants $C$, $r \in (0, 1]$ independent of $n$. If $2r\alpha > b > 1$, a random point from this density is Fisher-separable from $Y$ with probability $1 - \psi$, where $\psi < C\,(b/(2r\alpha))^n$. If the points of $Y$ themselves are drawn independently from such densities and $2r\alpha > b^2 > 1$, then $Y$ is Fisher-separable with probability $1 - \psi$, $\psi < C\,(b^2/(2r\alpha))^n$. So exponentially large random sets are separable by simple linear functionals with probability tending to one.

**Theorem 2 (explicit bound on the sphere).** Let $y \in S^{n-1}$, $n \ge 4$, and let $x$ be drawn from a rotationally invariant distribution on $S^{n-1}$. The probability that $x$ is not Fisher-separable from $y$ satisfies

$$p_y(\alpha) < \frac{(1 - \alpha^2)^{(n-1)/2}}{\alpha \sqrt{2\pi (n-1)}},$$

and this bound is asymptotically exact as $n \to \infty$. Consequently, if $Y$ is an i.i.d. sample from such a distribution and $0 < \psi < 1$, then

$$|Y| \frac{(1 - \alpha^2)^{(n-1)/2}}{\alpha\sqrt{2\pi(n-1)}} < \psi \ \Rightarrow\ \text{all sample points are separable from a given } y \text{ w.p.} > 1 - \psi, \qquad |Y|^2 \frac{(1 - \alpha^2)^{(n-1)/2}}{\alpha\sqrt{2\pi(n-1)}} < \psi \ \Rightarrow\ Y \text{ is Fisher-separable w.p.} > 1 - \psi .$$

**Neuroscience reading.** A single neuron receiving many effective inputs acts as a linear threshold unit; by these estimates, a few dozen effective dimensions already let one neuron respond selectively to one stimulus pattern against very large stimulus sets, which is offered as a mechanism for highly selective "concept cells" in the medial temporal lobe and for fast, non-destructive learning of new items with Hebbian (generalized Oja) plasticity.

## Expansion

On the sphere, $(x, x) = 1$, so the non-separable points form the cap $\{x : (x, y) > \alpha\}$, whose base has radius $\sqrt{1 - \alpha^2}$. Its area is less than the lateral area of the tangent cone over the same base, whose slant length is $\sqrt{1-\alpha^2}/\alpha$, giving

$$p_y(\alpha) < \frac{A_{n-2}}{A_{n-1}} \cdot \frac{(1-\alpha^2)^{(n-1)/2}}{\alpha (n-1)}, \qquad A_{m} = \frac{2\pi^{(m+1)/2}}{\Gamma\big(\tfrac{m+1}{2}\big)} .$$

Then $A_{n-2}/A_{n-1} = \Gamma(n/2)/\big(\sqrt\pi\, \Gamma((n-1)/2)\big)$, and log-convexity of $\Gamma$ with $\Gamma(x+1) = x\Gamma(x)$ gives $\Gamma(n/2)/\Gamma((n-1)/2) < \sqrt{(n-1)/2}$ for $n \ge 4$, which yields the bound. The sample-size criteria follow from the union bound over $|Y|$ (or $|Y|^2$ ordered pairs) events. With $\alpha = 0.8$ and $\psi = 0.01$, the guaranteed separable sample size grows very rapidly with $n$, so dimensions of $30$ to $50$ already count as high; for example, an i.i.d. uniform sample of $2.7 \times 10^6$ points in the $100$-dimensional ball is Fisher-separable with probability above $0.99$. Comparing the empirical distribution of $p_y(\alpha)$ with this formula defines an effective data dimension that is robust to noise and non-i.i.d. structure.

## Sources

- A. N. Gorban, V. A. Makarov, I. Y. Tyukin, "High-dimensional brain in a high-dimensional world: blessing of dimensionality", Entropy 22 (2020), 82, Section 2 (Definitions 1–2, Eqs. (1)–(3), Theorems 1–2), Section 4 (Eqs. (5)–(14), Table 1) and Section 5 (concept cells, hippocampal CA1 model), <https://doi.org/10.3390/e22010082> (PMC7516518).
