# Laplace transform of a causal convolution

Let $E$ be a complex Banach space, let $h : \mathbb{R} \to \mathbb{C}$ and $x : \mathbb{R} \to E$ be locally integrable and zero on $(-\infty, 0)$, and suppose there are $M \ge 0$ and $\sigma_0 \in \mathbb{R}$ with $|h(t)| \le M e^{\sigma_0 t}$ and $\|x(t)\| \le M e^{\sigma_0 t}$ for almost every $t \ge 0$. Let $(h * x)(t) = \int_0^t h(\tau)\, x(t - \tau)\, d\tau$ for $t \ge 0$ and $(h * x)(t) = 0$ for $t < 0$. Then for every $s \in \mathbb{C}$ with $\operatorname{Re} s > \sigma_0$, the one-sided Laplace transforms of $h$, $x$ and $h * x$ converge at $s$, and

$$\mathcal{L}(h * x)(s) = \mathcal{L}h(s)\, \mathcal{L}x(s).$$

For a matrix-valued kernel acting on vector signals the same identity holds with the matrix product taken in the order $\mathcal{L}h(s)\,\mathcal{L}x(s)$, applying the scalar case entrywise.

**Proof.** Let $\sigma = \operatorname{Re} s$. On the triangle $\{(\tau, t) : 0 \le \tau \le t\}$,

$$\iint |h(\tau)|\, \|x(t - \tau)\|\, e^{-\sigma t}\, d\tau\, dt = \int_0^\infty |h(\tau)| e^{-\sigma\tau}\, d\tau \int_0^\infty \|x(u)\| e^{-\sigma u}\, du < \infty$$

by Tonelli's theorem and the substitution $u = t - \tau$. So $e^{-st} h(\tau) x(t - \tau)$ is integrable on the triangle; by Fubini's theorem, integrating first in $\tau$ gives $\mathcal{L}(h * x)(s)$ (in particular $h * x$ is defined for almost every $t$ and its transform converges), and integrating first in $t$ gives $\int_0^\infty h(\tau) e^{-s\tau} \int_0^\infty e^{-su} x(u)\, du\, d\tau = \mathcal{L}h(s)\, \mathcal{L}x(s)$.

## Proof depends on

- [Convergence of the Laplace transform under an exponential bound](laplace-convergent-of-norm-le-exp.md): convergence of $\mathcal{L}h$ and $\mathcal{L}x$ for $\operatorname{Re} s > \sigma_0$

## Sources

- M. Vetterli, J. Kovačević and V. K. Goyal, *Foundations of Signal Processing*, Cambridge University Press, 2014 (free version v1.1), <https://fourierandwavelets.org/FSP_v1.1_2014.pdf>, Section 4.4.6, Definition 4.12 (Laplace transform, p. 379) and Table 4.2, the convolution property $(h * x)(t) \leftrightarrow H(s) X(s)$ with region of convergence containing $\mathrm{ROC}_h \cap \mathrm{ROC}_x$ (p. 380). The one-sided causal statement with exponential bounds and the Fubini proof are on the page.
