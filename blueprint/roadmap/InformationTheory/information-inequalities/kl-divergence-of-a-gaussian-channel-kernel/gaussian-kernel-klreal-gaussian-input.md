# Gaussian Kernel KLReal gaussian Input

Let $\kappa$ and $\iota$ be finite index sets with $d = \lvert \iota \rvert$, let $H$ be a real $\iota \times \kappa$ matrix, $q \in \mathbb{R}^{\iota}$, and $R, T$ any real $\iota \times \iota$ matrices. Let $m \in \mathbb{R}^{\kappa}$ and let $S$ be a positive semidefinite (possibly singular) real $\kappa \times \kappa$ matrix. At the Gaussian input $\mathcal{N}(m, S)$ the Gaussian channel kernel closed form is

$$\frac{1}{2}\left(\log\frac{\det T}{\det R} - d + \operatorname{tr}(T^{-1} R) + \operatorname{tr}\big(T^{-1} H S H^{\top}\big) + (H m - q)^{\top} T^{-1} (H m - q)\right),$$

with the conventions $x/0 = 0$, $\log 0 = 0$ and $T^{-1} = 0$ for singular $T$.
