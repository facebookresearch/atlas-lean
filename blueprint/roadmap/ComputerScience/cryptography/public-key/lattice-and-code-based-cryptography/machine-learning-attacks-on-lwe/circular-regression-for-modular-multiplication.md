# Circular regression loss for one-dimensional LWE

One-dimensional LWE $b_i\equiv a_is+e_i \pmod p$ becomes a regression on the circle by mapping $b_i$ to the angle class of $2\pi b_i/p$. A discrete von Mises model on the $p$ angle classes leads to the loss $-\sum_i\cos(y_i-2\pi a_is/p)$, bounded below by $-m$, which gradient descent over a real relaxation of $s$ attempts to minimise.

Let $p$ be prime, $s\in\{0,\dots,p-1\}$ unknown, and $(a_i,b_i)$, $i=1,\dots,m$, integer pairs with $b_i\equiv a_is+e_i \pmod p$ and $e_i$ from a centred discrete Gaussian. Put $y_i=2\pi b_i/p$; only its class modulo $2\pi$ matters below, since every expression is $2\pi$-periodic in $y_i$.

**Grid likelihood.** The von Mises density on $[-\pi,\pi]$ with location $\mu$ and concentration $\kappa>0$ is $f(\theta\mid\mu,\kappa)=\exp(\kappa\cos(\theta-\mu))/(2\pi I_0(\kappa))$, with $I_0$ the modified Bessel function of order $0$. Lauter et al. model each $y_i$ as a discrete von Mises variable with location $\mu_i=2\pi a_is/p$ and common $\kappa$. Take its support to be the $p$ angle classes $2\pi k/p$, $k\in\mathbb{Z}/p\mathbb{Z}$, with mass $c\,f(2\pi k/p\mid\mu,\kappa)$. For $\mu\in(2\pi/p)\mathbb{Z}$, rotating by $\mu$ permutes these classes, so the normaliser $c^{-1}=\sum_{k\in\mathbb{Z}/p\mathbb{Z}}f(2\pi k/p\mid\mu,\kappa)$ does not depend on $\mu$. (The integer range $[-(p+1)/2,(p-1)/2]$ printed in the source contains $p+1$ integers for odd $p$, two of which give the same angle class; the model is taken on the $p$ distinct classes.) For integer $s$ the log-likelihood is $\kappa\sum_i\cos(y_i-\mu_i)$ plus terms independent of $s$, so maximum likelihood over integer $s$ minimises

$$
\mathcal{L}(s)=-\sum_{i=1}^{m}\cos\Bigl(y_i-\frac{2\pi}{p}a_is\Bigr).
$$

**Real relaxation.** The same expression, for real $s$, is used as a surrogate loss (it is no longer a normalised likelihood). It satisfies $\mathcal{L}(s)\ge-m$, with equality exactly when every cosine equals $1$, which happens at the true secret for noiseless data but need not happen at any $s$ for noisy data. Gradient descent uses

$$
s_{t+1}=s_t+\eta\,\frac{2\pi}{p}\sum_{i=1}^{m}a_i\sin\Bigl(y_i-\frac{2\pi}{p}a_is_t\Bigr)
$$

with learning rate $\eta>0$, halts once $\mathcal{L}(s_t)\le-m+\varepsilon$ for a chosen tolerance $\varepsilon$ (a condition that may never be met on noisy data), and outputs the integer in $(s_t-\frac12,s_t+\frac12]$.

## Expansion

The update is gradient descent on $\mathcal{L}$, since $\mathcal{L}'(s)=-\frac{2\pi}{p}\sum_ia_i\sin(y_i-\frac{2\pi}{p}a_is)$. On noiseless data with all $a_i\in\{0,\dots,p-1\}$ the authors plot the loss for several primes and observe a deep valley at the secret with oscillations of decreasing size elsewhere; that shape is an observation for those examples. They report that the method, as implemented, does not consistently improve on exhaustive search; this is an experimental result, not a hardness theorem.

## Depends on

None.

## Proof depends on

None.

## Sources

- Kristin Lauter, Cathy Yuanchen Li, Krystal Maughan, Rachel Newton, Megha Srivastava, "Machine Learning for Modular Multiplication", in Research Directions in Number Theory, Association for Women in Mathematics Series 39, Springer, 2026, https://doi.org/10.1007/978-3-032-11183-8_9, Section 2 (Definition 1, Sections 2.1–2.3, Figure 1).
