# The exponential of a screw motion and the product-of-exponentials formula

For $\omega, v \in \mathbb{R}^3$ let $[\mathcal{S}] = \begin{bmatrix} [\omega] & v \\ 0 & 0 \end{bmatrix} \in \mathbb{R}^{4 \times 4}$ for the screw axis $\mathcal{S} = (\omega, v)$, and let $\theta \in \mathbb{R}$.

1. **Rotational screw.** If $\|\omega\| = 1$, then

    $$e^{[\mathcal{S}]\theta} = \begin{bmatrix} e^{[\omega]\theta} & \big(I\theta + (1 - \cos\theta)[\omega] + (\theta - \sin\theta)[\omega]^2\big) v \\ 0 & 1 \end{bmatrix}.$$

2. **Translational screw.** If $\omega = 0$ and $\|v\| = 1$, then $e^{[\mathcal{S}]\theta} = \begin{bmatrix} I & v\theta \\ 0 & 1 \end{bmatrix}$.
3. **Rigid motions.** In both cases $e^{[\mathcal{S}]\theta}$ lies in $\mathrm{SE}(3)$, the group of matrices $\begin{bmatrix} R & p \\ 0 & 1 \end{bmatrix}$ with $R \in \mathrm{SO}(3)$ and $p \in \mathbb{R}^3$.
4. **Product of exponentials.** Consider an open chain of $n$ one-degree-of-freedom joints whose end-effector frame is $M \in \mathrm{SE}(3)$ in the home position $\theta = 0$, and let $\mathcal{S}_i$ be the screw axis of joint $i$, expressed in the fixed frame with all joints at home. If moving joint $i$ alone by $\theta_i$, with joints $i+1, \dots, n$ already displaced, moves the distal links by the rigid motion $e^{[\mathcal{S}_i]\theta_i}$ applied on the left, then the end-effector frame is

    $$T(\theta) = e^{[\mathcal{S}_1]\theta_1} e^{[\mathcal{S}_2]\theta_2} \cdots e^{[\mathcal{S}_n]\theta_n} M .$$

**Proof.** Powers of $[\mathcal{S}]$ have upper-left block $[\omega]^k$ and upper-right block $[\omega]^{k-1} v$, so $e^{[\mathcal{S}]\theta}$ has blocks $e^{[\omega]\theta}$ and $G(\theta) v$ with $G(\theta) = \sum_{k \ge 1} [\omega]^{k-1}\theta^k / k!$. Using $[\omega]^3 = -[\omega]$ for $\|\omega\| = 1$ and collecting odd and even powers gives $G(\theta) = I\theta + (1 - \cos\theta)[\omega] + (\theta - \sin\theta)[\omega]^2$, which is part 1; for $\omega = 0$ only the $k = 1$ term survives, part 2. Part 3 follows from Rodrigues' formula. For part 4, displace the joints in the order $n, n-1, \dots, 1$: each displacement acts on the configuration reached so far by left multiplication with $e^{[\mathcal{S}_i]\theta_i}$, since the axis of joint $i$ has not yet moved when it is displaced, which gives the product.

## Proof depends on

- [Rodrigues' formula and exponential coordinates of rotations](rodrigues-formula-and-exponential-coordinates-of-rotations.md): the rotation block $e^{[\omega]\theta} \in \mathrm{SO}(3)$

## Sources

- K. M. Lynch and F. C. Park, *Modern Robotics: Mechanics, Planning, and Control*, Cambridge University Press, 2017 (preprint, <http://modernrobotics.org>), Section 3.3.3: Proposition 3.25, the exponential (3.88) of a screw axis with $\|\omega\| = 1$ and its translational case (3.89) (pp. 105–106); Section 4.1.1: the space form of the product of exponentials formula (4.14) and its derivation by displacing the joints from the distal end (p. 142). The series computation is on the page.
