# Identities of planar rotation matrices

For all $a, b, \theta \in \mathbb{R}$, the [rotation matrices](real-planar-rotation-matrices.md) $R(\theta)$ satisfy:

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

## Depends on

- [Real planar rotation matrices](real-planar-rotation-matrices.md)

## Sources

- J. Su, Y. Lu, S. Pan, A. Murtadha, B. Wen and Y. Liu, "RoFormer: Enhanced Transformer with Rotary Position Embedding", arXiv:2104.09864 (version 5), Section 3.2.1, equations (12)–(13): the rotation matrix and its complex form $e^{im\theta}$, with the inner product as the real part of $z \bar{w}$. The identities themselves are derived here.
