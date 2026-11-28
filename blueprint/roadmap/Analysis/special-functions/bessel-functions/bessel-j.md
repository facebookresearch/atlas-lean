# Bessel function of the first kind

For real order $\nu$ and complex argument $z$, the Bessel function of the first kind is the series

$$J_\nu(z) = \sum_{k \ge 0} \frac{(-1)^k}{k!\, \Gamma(\nu + k + 1)} \Bigl(\frac z2\Bigr)^{2k + \nu},$$

with the complex power taken on the principal branch. Two conventions of the linked definition matter. At a pole of $\Gamma$ (when $\nu + k + 1$ is a nonpositive integer) the Gamma value is read as $0$ and so is the coefficient, matching the zeros of $1/\Gamma$. At $z = 0$ the complex power $0^w$ is $0$ for $w \ne 0$ and $1$ for $w = 0$; for example the series gives $J_{-1/2}(0) = 0$, whereas the classical $J_{-1/2}(x) = \sqrt{2/(\pi x)}\cos x$ diverges as $x \to 0^+$.
