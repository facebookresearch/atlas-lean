# The angular velocity matrix of a rotating frame is skew-symmetric

Let $R : J \to \mathbb{R}^{n \times n}$ be differentiable on an interval $J$ with $R(t) R(t)^\top = I_n$ for every $t \in J$. Then the
angular velocity matrix $W(t) = R'(t) R(t)^\top$ is skew-symmetric, $W(t)^\top = -W(t)$, for every $t \in J$. For a fixed vector
$a \in \mathbb{R}^n$, the moving point $r(t) = R(t) a$ satisfies $r'(t) = W(t) r(t)$. For $n = 3$ there is a unique $\omega(t) \in \mathbb{R}^3$
with $W(t) x = \omega(t) \times x$ for all $x$, so $r' = \omega \times r$, the rigid plate velocity. Positions are measured from the fixed
origin about which the frame rotates.

Proof: differentiating $R R^\top = I_n$ gives $R' R^\top + R (R')^\top = 0$, that is $W + W^\top = 0$. Since $R^\top$ is a right inverse of
the square matrix $R$, it is also a left inverse, so $r' = R' a = R' R^\top R a = W r$. A skew-symmetric $3 \times 3$ matrix has the form
$\begin{pmatrix} 0 & -\omega_3 & \omega_2 \\ \omega_3 & 0 & -\omega_1 \\ -\omega_2 & \omega_1 & 0 \end{pmatrix}$, which acts as $x \mapsto \omega \times x$.

## Sources

- Wikipedia, "Angular velocity tensor", revision of 11 September 2026: the definition of the skew-symmetric matrix $\Omega$ and its
  vector $\omega$, the section "Ω is skew-symmetric", and the rigid-body derivation of $\mathbf{V}_i = \mathbf{V} + \Omega\,\mathbf{r}_i$ with
  $\Omega = \frac{d\mathcal{R}}{dt} \mathcal{R}^{\mathsf{T}}$.
