# Rodrigues' formula and exponential coordinates of rotations

For $\omega \in \mathbb{R}^3$ let $[\omega]$ be the skew-symmetric matrix with $[\omega] x = \omega \times x$. Let $\hat\omega \in \mathbb{R}^3$ be a unit vector and $\theta \in \mathbb{R}$.

1. **Rodrigues' formula.** $e^{[\hat\omega]\theta} = I + \sin\theta\, [\hat\omega] + (1 - \cos\theta)\, [\hat\omega]^2$.
2. **Rotations.** $e^{[\hat\omega]\theta}$ lies in $\mathrm{SO}(3)$: it is orthogonal with determinant $1$; it fixes $\hat\omega$ and rotates the plane orthogonal to $\hat\omega$ by the angle $\theta$.
3. **Exponential coordinates.** Every $R \in \mathrm{SO}(3)$ is of this form: there are a unit vector $\hat\omega$ and $\theta \in [0, \pi]$ with $R = e^{[\hat\omega]\theta}$, and $\operatorname{tr} R = 1 + 2\cos\theta$. For $R \ne I$ and $\operatorname{tr} R \ne -1$ the pair is unique, with $[\hat\omega] = (R - R^\top)/(2\sin\theta)$.

**Proof.** For a unit vector, $[\hat\omega]^3 = -[\hat\omega]$, so the exponential series splits into odd and even powers with coefficients the series of $\sin\theta$ and $1 - \cos\theta$, which is part 1. For part 2, $[\hat\omega]^\top = -[\hat\omega]$ gives $(e^{[\hat\omega]\theta})^\top e^{[\hat\omega]\theta} = e^{-[\hat\omega]\theta} e^{[\hat\omega]\theta} = I$, and $\det e^{[\hat\omega]\theta} = e^{\operatorname{tr}[\hat\omega]\theta} = 1$; $[\hat\omega]\hat\omega = 0$, and on a vector $x \perp \hat\omega$ the formula gives $\cos\theta\, x + \sin\theta\, \hat\omega \times x$. For part 3, an orthogonal $3 \times 3$ matrix of determinant $1$ has the eigenvalue $1$, since $\det(R - I) = \det(R^\top)\det(R - I) = \det(I - R^\top) = -\det(R - I)$; take a unit eigenvector $\hat\omega$. $R$ preserves the plane orthogonal to $\hat\omega$ and acts there as an orientation-preserving isometry, a rotation by some angle, which may be taken in $[0, \pi]$ after replacing $\hat\omega$ by $-\hat\omega$. The trace formula follows from part 1 and $\operatorname{tr}[\hat\omega]^2 = -2$, and the uniqueness statement from $R - R^\top = 2\sin\theta\,[\hat\omega]$.

## Sources

- K. M. Lynch and F. C. Park, *Modern Robotics: Mechanics, Planning, and Control*, Cambridge University Press, 2017 (preprint, <http://modernrobotics.org>), Section 3.2.3: Proposition 3.11 and (3.51), Rodrigues' formula $e^{[\hat\omega]\theta} = I + \sin\theta[\hat\omega] + (1 - \cos\theta)[\hat\omega]^2 \in \mathrm{SO}(3)$ (p. 84), and the matrix logarithm of rotations in Section 3.2.3.3. The eigenvector argument for surjectivity is written out on the page.
