# Gaussian Kernel KLReal dirac

Let $\kappa$ and $\iota$ be finite index sets with $d = \lvert \iota \rvert$, let $H$ be a real $\iota \times \kappa$ matrix, $q \in \mathbb{R}^{\iota}$, $R, T$ any real $\iota \times \iota$ matrices and $a \in \mathbb{R}^{\kappa}$. At the point-mass input $\delta_a$ the expected quadratic form is the quadratic form at $a$, so the Gaussian channel kernel closed form is

$$\frac{1}{2}\left(\log\frac{\det T}{\det R} - d + \operatorname{tr}(T^{-1} R) + (H a - q)^{\top} T^{-1} (H a - q)\right),$$

with the conventions $x/0 = 0$, $\log 0 = 0$, $\log x = \log\lvert x\rvert$ for $x < 0$, and $T^{-1} = 0$ for singular $T$.
