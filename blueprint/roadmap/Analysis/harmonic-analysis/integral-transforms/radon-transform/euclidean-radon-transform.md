# Euclidean Radon transform

For $n \in \mathbb{N}$, $f : \mathbb{R}^n \to \mathbb{R}$, a direction $\xi \in \mathbb{R}^n$ and $t \in \mathbb{R}$, the Euclidean Radon transform is

$$Rf(\xi, t) = \int_{\{x \in \mathbb{R}^n : \langle x, \xi\rangle = t\}} f(x)\, d\mathcal{H}^{n-1}(x),$$

with $\mathcal{H}^{n-1}$ the Euclidean Hausdorff measure of the natural-number dimension $n - 1$ (dimension $0$ when $n = 0$). The integral is a Bochner integral, read as $0$ when $f$ is not integrable on the level set: for $f = 1$ and a line in $\mathbb{R}^2$ the classical integral diverges and the value is $0$. The level set is a hyperplane only for $\xi \ne 0$; for a unit $\xi$, $t$ is its signed distance from the origin.
