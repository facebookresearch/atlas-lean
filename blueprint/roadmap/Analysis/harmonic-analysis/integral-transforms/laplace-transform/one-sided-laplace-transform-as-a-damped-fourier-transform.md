# The one-sided Laplace transform as a damped Fourier transform

Let $E$ be a complex Banach space, $x : \mathbb{R} \to E$ and $\sigma \in \mathbb{R}$, and suppose $g(t) = \mathbf{1}_{(0, \infty)}(t)\, x(t)\, e^{-\sigma t}$ is integrable on $\mathbb{R}$. With the Fourier transform $\mathcal{F}g(\xi) = \int_{\mathbb{R}} e^{-2\pi i \xi t} g(t)\, dt$, the one-sided Laplace transform of $x$ converges at every $s$ on the vertical line $\operatorname{Re} s = \sigma$, and

$$\mathcal{L}x(\sigma + 2\pi i \xi) = \mathcal{F}g(\xi) \qquad \text{for every } \xi \in \mathbb{R}.$$

Consequently $\xi \mapsto \mathcal{L}x(\sigma + 2\pi i\xi)$ is bounded by $\|g\|_1$ and continuous. This is an identity on a line where the damped signal is integrable, not a statement about boundary limits of $\mathcal{L}x$ from the right half-plane.

**Proof.** For $s = \sigma + 2\pi i \xi$, $|e^{-st}| = e^{-\sigma t}$, so $t \mapsto e^{-st} x(t)$ is integrable on $(0, \infty)$ exactly when $g$ is integrable, and $e^{-st} x(t) = e^{-2\pi i \xi t} g(t)$ for $t > 0$, while $g = 0$ on $(-\infty, 0]$. The bound and continuity are those of the Fourier transform of an integrable function.

## Depends on

- [Convergence of the Laplace transform](laplace-convergent.md): absolute convergence of the one-sided transform

## Sources

- M. Vetterli, J. Kovačević and V. K. Goyal, *Foundations of Signal Processing*, Cambridge University Press, 2014 (free version v1.1), <https://fourierandwavelets.org/FSP_v1.1_2014.pdf>, Section 4.4.6, Definition 4.12 and (4.90) (p. 379): $X(\sigma + j\omega)$ is the Fourier transform of $x(t)e^{-\sigma t}$, and for $\sigma$ with $x(t)e^{-\sigma t}$ absolutely integrable the transform is bounded and continuous. The source uses the two-sided transform and angular frequency $\omega = 2\pi\xi$; the one-sided form with the normalization $e^{-2\pi i \xi t}$ is stated on the page.
