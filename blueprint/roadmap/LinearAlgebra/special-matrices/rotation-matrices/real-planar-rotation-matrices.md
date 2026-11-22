# Real planar rotation matrices

For $\theta \in \mathbb{R}$, the rotation matrix through the angle $\theta$ is
$R(\theta) = \begin{pmatrix} \cos\theta & -\sin\theta \\ \sin\theta & \cos\theta \end{pmatrix}
\in \mathbb{R}^{2 \times 2}$. For all $a, b, \theta \in \mathbb{R}$:

- $R(a) R(b) = R(a + b)$;
- $R(\theta)^{\mathsf{T}} = R(-\theta) = R(\theta)^{-1}$, so $R(\theta)$ is orthogonal,
  $\det R(\theta) = 1$ and $\|R(\theta) x\|_2 = \|x\|_2$ for every $x \in \mathbb{R}^2$;
- consequently $R(a)^{\mathsf{T}} R(b) = R(b - a)$;
- identifying $(x, y) \in \mathbb{R}^2$ with $x + iy \in \mathbb{C}$, $R(\theta)$ acts as
  $z \mapsto e^{i\theta} z$, and the Euclidean inner product is
  $\langle z, w \rangle = \operatorname{Re}(z \bar{w})$.

Proof: multiplying out $R(a) R(b)$ and using the angle-addition formulas
$\cos(a + b) = \cos a \cos b - \sin a \sin b$ and $\sin(a + b) = \sin a \cos b + \cos a \sin b$
gives $R(a + b)$. Since $\cos$ is even and $\sin$ is odd, transposing $R(\theta)$ gives
$R(-\theta)$, and $R(-\theta) R(\theta) = R(0) = I$; then $\det R(\theta) = \cos^2\theta +
\sin^2\theta = 1$, and an orthogonal matrix preserves the Euclidean norm. Finally
$R(a)^{\mathsf{T}} R(b) = R(-a) R(b) = R(b - a)$, and
$e^{i\theta}(x + iy) = (x \cos\theta - y \sin\theta) + i (x \sin\theta + y \cos\theta)$.

Block-diagonal rotations: for an integer $k \ge 1$, angles $\theta_1, \dots, \theta_k$ and
$m \in \mathbb{R}$, let $R_{\Theta}(m) \in \mathbb{R}^{2k \times 2k}$ be the block-diagonal matrix
with the blocks $R(m \theta_1), \dots, R(m \theta_k)$. Applying the facts above block by block,
$R_{\Theta}(m)$ is orthogonal and $R_{\Theta}(m)^{\mathsf{T}} R_{\Theta}(n) = R_{\Theta}(n - m)$ for
all $m, n \in \mathbb{R}$.
