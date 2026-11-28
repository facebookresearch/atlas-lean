# Survival of dispersing colonies under uniform catastrophes

**Model.** Colonies grow and suffer uniform catastrophes as in [survivors of a uniform catastrophe](survivors-of-a-uniform-catastrophe.md): births at rate $\lambda$, catastrophes at rate 1, survivors uniform on $\{0, \dots, i-1\}$ for a colony of size $i$. After a catastrophe the survivors leave and try to found new colonies of size one.

- $C_d(\lambda)$ (spatial restriction): colonies live on the rooted tree $\mathbb{T}^+_d$ (root degree $d$, other vertices degree $d+1$), starting from one individual at the root. Each survivor picks one of the $d$ children of its vertex uniformly at random; among survivors choosing the same child only one founds a colony, so a catastrophe replaces a colony by $0, 1, \dots, d$ colonies. Let $\psi_d$ be its extinction probability.
- $C_\ast(\lambda)$ (no spatial restriction): every survivor founds its own new colony, independently. Let $\psi_\ast$ and $\tau_\ast$ be its extinction probability and extinction time.

**Statement.**

1. Let $d \ge 2$. Then $C_d(\lambda)$ survives ($\psi_d < 1$) if and only if

$$\frac{d^2}{d-1}\ln\Big(\frac{\lambda + d}{d}\Big) < \lambda.$$

(For $d = 1$ the left side is undefined. There a catastrophe replaces a colony by at most one colony, and by none with positive probability, so $C_1(\lambda)$ dies out for every $\lambda > 0$.)

For $d = 2$ this reads $4\ln(1 + \lambda/2) < \lambda$, and then

$$\psi_2 = \min\Big\{1, \frac{\ln(\lambda+1)}{\lambda + \ln(\lambda+1) - 4\ln(1 + \lambda/2)}\Big\};$$

for $d = 3$ it reads $\tfrac92\ln(1 + \lambda/3) < \lambda$, and then, with

$$a = \frac{\ln(1+\lambda)}{\lambda}, \qquad b = \frac{1}{2\lambda}\ln\Big(1 + \frac{2\lambda}{3}\Big), \qquad c = \frac1\lambda\ln\Big(1 + \frac\lambda3\Big),$$

$\psi_3$ is the smallest nonnegative root of $(a - 9b + 9c - 1)s^2 - (1 + 2a - 9b)s + a = 0$ (capped at $1$), namely

$$\psi_3 = \min\Big\{1, \frac{1 + 2a - 9b - \sqrt{(1 - 9b)^2 + 4a(2 - 9c)}}{2(a - 9b + 9c - 1)}\Big\}.$$

The source's Theorem 2.5 prints $+\sqrt{\cdots}$; that root is negative in the supercritical regime (for $\lambda = 10$ the two roots are about $-1.93$ and $0.349$), so the extinction probability is the root with $-\sqrt{\cdots}$. The critical rate $\lambda_d = \inf\{\lambda : C_d(\lambda) \text{ survives}\}$ decreases in $d$ toward $2$.
2. $C_\ast(\lambda)$ survives if and only if $\lambda > 2$; then $\psi_\ast$ is the smallest nonnegative solution $s$ of $\ln\big(1 + \lambda(1-s)\big) = \lambda s(1-s)$. For $\lambda \le 2$,

$$\mathbb{E}[\tau_\ast] = \frac1\lambda\int_0^\lambda \frac{x^2}{\lambda\ln(1+x) - x(\lambda - x)}\,dx .$$

3. In the subcritical regime $4\ln(1+\lambda/2) > \lambda$, $C_2(\lambda)$ has mean extinction time $\mathbb{E}[\tau_2] = \beta^{-1}\ln\big(\alpha/(\alpha - \beta)\big)$ with $\alpha = \ln(\lambda+1)/\lambda$ and $\beta = 1 - \lambda^{-1}\ln\big((\lambda+2)^4/(16(\lambda+1))\big)$, and $\mathbb{E}[\tau_2] = \infty$ at criticality.

## Depends on

- [Survivors of a uniform catastrophe](survivors-of-a-uniform-catastrophe.md)

## Expansion

Colonies evolve independently, so the number of colonies is a continuous-time Galton–Watson process whose offspring is the number of distinct children chosen by the survivors. In $C_\ast$ the offspring is $N$ itself, with mean $\lambda/2$, so survival holds exactly when $\lambda > 2$, and $\psi_\ast$ is the smallest fixed point of $\mathbb{E}(s^N) = \ln(1+\lambda(1-s))/(\lambda(1-s))$, which rearranges to the stated equation. In $C_d$, given $N = n$ the number of occupied children is the number of occupied boxes when $n$ balls go into $d$ boxes, with mean $d\big(1 - (1 - 1/d)^n\big)$; averaging with the generating function of $N$ at $s = 1 - 1/d$ gives mean offspring $d - \frac{d^2}{\lambda}\ln\big(1 + \frac{\lambda}{d}\big)$, and for $d \ge 2$ the criterion mean $> 1$ is exactly the stated inequality (dividing by $d - 1$), while for $d = 1$ the mean $1 - \ln(1+\lambda)/\lambda$ is below $1$ for every $\lambda$. Mean extinction times follow from integrating the backward equation of the colony-count process.

## Sources

- J. Amaya, V. V. Junior, F. P. Machado and A. Roldán-Correa, "Growth models under uniform catastrophes", *Journal of Statistical Physics* 193(11) (2026), 162, Theorems 2.3, 2.4, 2.5, 2.6 and 2.8; Remark 2.7 (Theorem 2.4 is stated without a range for $d$, but its criterion divides by $d - 1$, so it is restricted here to $d \ge 2$), <https://doi.org/10.1007/s10955-026-03718-8> (preprint arXiv:2602.06649).
