# The space Jacobian of the product-of-exponentials formula

Let $T(\theta) = e^{[\mathcal{S}_1]\theta_1} \cdots e^{[\mathcal{S}_n]\theta_n} M$ be the forward kinematics of an open chain given by the product-of-exponentials formula, with screw axes $\mathcal{S}_i = (\omega_i, v_i)$ and $M \in \mathrm{SE}(3)$. For $T = \begin{bmatrix} R & p \\ 0 & 1 \end{bmatrix} \in \mathrm{SE}(3)$ let $\mathrm{Ad}_T$ be the linear map on $\mathbb{R}^6$ with $[\mathrm{Ad}_T \mathcal{V}] = T[\mathcal{V}]T^{-1}$, that is $\mathrm{Ad}_T(\omega, v) = (R\omega, [p]R\omega + Rv)$. Then:

1. **Space twist.** For every differentiable joint trajectory $\theta(t)$, $\dot T T^{-1} = [\mathcal{V}_s]$ with $\mathcal{V}_s = J_s(\theta)\dot\theta$, where the $i$-th column of the space Jacobian $J_s(\theta) \in \mathbb{R}^{6 \times n}$ is

    $$J_{s,1} = \mathcal{S}_1, \qquad J_{s,i}(\theta) = \mathrm{Ad}_{e^{[\mathcal{S}_1]\theta_1} \cdots e^{[\mathcal{S}_{i-1}]\theta_{i-1}}}(\mathcal{S}_i) \quad (i \ge 2).$$

2. **Derivative of the forward kinematics.** The map $\theta \mapsto T(\theta)$ is smooth, and its derivative at $\theta$ applied to $\dot\theta \in \mathbb{R}^n$ is $[J_s(\theta)\dot\theta]\, T(\theta)$. So the geometric Jacobian $J_s$ is the derivative of the forward kinematics, read through right translation to the identity.

**Proof.** Write $E_i = e^{[\mathcal{S}_i]\theta_i}$, so $\frac{d}{dt}E_i = [\mathcal{S}_i]\dot\theta_i E_i$. By the product rule,

$$\dot T T^{-1} = \sum_{i=1}^n E_1 \cdots E_{i-1}[\mathcal{S}_i] E_{i-1}^{-1} \cdots E_1^{-1}\,\dot\theta_i = \sum_{i=1}^n \big[\mathrm{Ad}_{E_1 \cdots E_{i-1}}(\mathcal{S}_i)\big]\dot\theta_i ,$$

the factors $E_{i+1} \cdots E_n M$ cancelling against their inverses. The formula for $\mathrm{Ad}_T$ follows by multiplying out $T[\mathcal{V}]T^{-1}$ and using $R[\omega]R^\top = [R\omega]$. Part 2 is part 1 for the straight lines $\theta(t) = \theta + t\dot\theta$, smoothness coming from that of the matrix exponential.

## Proof depends on

- [The exponential of a screw motion and the product-of-exponentials formula](the-exponential-of-a-screw-motion-and-the-product-of-exponentials-formula.md): the forward kinematics and the rigid motions $e^{[\mathcal{S}_i]\theta_i}$

## Sources

- K. M. Lynch and F. C. Park, *Modern Robotics: Mechanics, Planning, and Control*, Cambridge University Press, 2017 (preprint, <http://modernrobotics.org>), Definition 3.20 (the adjoint representation of a rigid motion) and Section 5.1.1, the space Jacobian $J_{si}(\theta) = \mathrm{Ad}_{e^{[\mathcal{S}_1]\theta_1}\cdots e^{[\mathcal{S}_{i-1}]\theta_{i-1}}}(\mathcal{S}_i)$ (5.11) and $\mathcal{V}_s = J_s(\theta)\dot\theta$ (p. 180). The identification with the derivative of the forward kinematics is stated on the page.
