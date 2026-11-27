# Radon transform on the plane

For $f : \mathbb{R}^2 \to \mathbb{C}$ and
$p, \theta \in \mathbb{R}$, the Radon transform of $f$ at $(p, \theta)$ is the integral of $f$
along the line $x \cos\theta + y \sin\theta = p$ with respect to arc length,

$$Rf(p, \theta) = \int_{\mathbb{R}} f(p\cos\theta - t\sin\theta, p\sin\theta + t\cos\theta)\,dt,$$

where the integral is taken to be $0$ when the integrand is not integrable.
