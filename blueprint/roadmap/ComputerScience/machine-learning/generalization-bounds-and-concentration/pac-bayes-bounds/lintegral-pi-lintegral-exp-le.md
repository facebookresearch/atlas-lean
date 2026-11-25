# Tonelli step

Let $\Theta$ and $\mathcal Z$ be measurable spaces, $\pi$ a probability measure on $\Theta$, $D$ a
probability measure on $\mathcal Z$, $\ell : \Theta \times \mathcal Z \to [0, C]$ jointly
measurable and $n \ge 1$. Write $R(\theta) = \int \ell(\theta, z) \, dD(z)$ and
$r_S(\theta) = \frac1n \sum_{i=1}^n \ell(\theta, S_i)$. Then for every real $\lambda$, with $S$ an
i.i.d. sample of size $n$ from $D$,

$$\mathbb{E}_S \int \exp\big(\lambda (R(\theta) - r_S(\theta))\big) \, d\pi(\theta) \le \exp\Big(\frac{\lambda^2 C^2}{8 n}\Big),$$

the integrals being taken in $[0, \infty]$.
