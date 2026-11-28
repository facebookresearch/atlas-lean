# Homogeneous transformation matrices represent rigid motions

Let $\mathrm{SE}(3)$ be the set of $4 \times 4$ matrices $T = \begin{bmatrix} R & p \\ 0 & 1 \end{bmatrix}$ with $R \in \mathrm{SO}(3)$ and $p \in \mathbb{R}^3$, written $T = (R, p)$, and let $T$ act on points by $Tx = Rx + p$.

1. **Group.** $\mathrm{SE}(3)$ is closed under multiplication, $(R_1, p_1)(R_2, p_2) = (R_1R_2,\ R_1p_2 + p_1)$, and under inversion, $(R, p)^{-1} = (R^\top, -R^\top p)$; multiplication is associative and in general not commutative.
2. **Homogeneous coordinates.** $T\begin{bmatrix} x \\ 1 \end{bmatrix} = \begin{bmatrix} Rx + p \\ 1 \end{bmatrix}$, so the matrix product $T_1T_2$ acts on points as the composition $x \mapsto T_1(T_2x)$, and $T^{-1}$ acts as the inverse map.
3. **Rigid motions.** Each map $x \mapsto Tx$ preserves distances, $\|Tx - Ty\| = \|x - y\|$, and angles, $\langle Tx - Tz, Ty - Tz\rangle = \langle x - z, y - z\rangle$, and preserves orientation.
4. **Frame bookkeeping.** If $T_{ab}$ denotes the matrix that converts the coordinates of a point in frame $b$ into its coordinates in frame $a$, $x_a = T_{ab}x_b$, then $T_{ac} = T_{ab}T_{bc}$ and $T_{ba} = T_{ab}^{-1}$: the inner frame labels of a product must match and cancel.

**Proof.** Part 1 is block multiplication: $R_1R_2 \in \mathrm{SO}(3)$, and $(R^\top, -R^\top p)(R, p) = (I, R^\top p - R^\top p) = (I, 0)$; for noncommutativity take two rotations about different axes. Part 2 is the block product with the vector $(x, 1)$ and part 1. In part 3, $Tx - Ty = R(x - y)$ and $R^\top R = I$ give both identities, and $\det R = 1$ gives orientation. In part 4, $x_a = T_{ab}x_b = T_{ab}T_{bc}x_c$ for every point, so $T_{ac} = T_{ab}T_{bc}$ by part 2, and $x_b = T_{ab}^{-1}x_a$ gives the inverse.

## Background

- [Rodrigues' formula and exponential coordinates of rotations](rodrigues-formula-and-exponential-coordinates-of-rotations.md): the rotation block $R$ and its exponential coordinates

## Sources

- K. M. Lynch and F. C. Park, *Modern Robotics: Mechanics, Planning, and Control*, Cambridge University Press, 2017 (preprint, <http://modernrobotics.org>), Section 3.3.1: Definition 3.13 of $\mathrm{SE}(3)$ (3.62) (p. 89), Propositions 3.15–3.17 (inverse (3.64), closure, associativity and noncommutativity) and homogeneous coordinates (3.65) (p. 90), and Proposition 3.18 (distances and angles are preserved, p. 91); the subscript cancellation rule for products of transformation matrices is used throughout Section 3.3.1. The proofs are on the page.
