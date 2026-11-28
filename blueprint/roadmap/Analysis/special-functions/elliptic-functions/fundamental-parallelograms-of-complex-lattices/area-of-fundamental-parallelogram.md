# Area of a fundamental parallelogram

Let $\omega_1, \omega_2$ be $\mathbb{R}$-linearly independent complex numbers, let
$\Lambda = \mathbb{Z}\omega_1 + \mathbb{Z}\omega_2$, let $\alpha \in \mathbb{C}$, and let
$P = \{\alpha + t_1 \omega_1 + t_2 \omega_2 : t_1, t_2 \in [0, 1)\}$ be the
[fundamental parallelogram](fundamental-parallelogram.md) with vertex $\alpha$. Identify $\mathbb{C}$
with $\mathbb{R}^2$ by $z = x + iy$, with Lebesgue measure $dx \, dy$.

**Theorem.**

1. The Lebesgue measure of $P$ is $|\operatorname{Im}(\bar\omega_1 \omega_2)|$. In particular, for
   $\omega_1 = 1$ and $\omega_2 = \tau$ with $\operatorname{Im} \tau > 0$, it is $\operatorname{Im} \tau$.
2. The translates $P + \lambda$, $\lambda \in \Lambda$, are pairwise disjoint and cover $\mathbb{C}$.

So $P$ maps bijectively onto $\mathbb{C}/\Lambda$, and for a constant $c \in \mathbb{C}$ the integral of
the translation-invariant form $\frac{i}{2} |c|^2 \, dz \wedge d\bar z = |c|^2 \, dx \wedge dy$ over
$\mathbb{C}/\Lambda$, with its orientation from $\mathbb{C}$, is $|c|^2 \, |\operatorname{Im}(\bar\omega_1 \omega_2)|$.

*Proof.* The real-linear map $(t_1, t_2) \mapsto t_1 \omega_1 + t_2 \omega_2$ takes $[0, 1)^2$ onto
$P - \alpha$; writing $\omega_k = a_k + i b_k$, its determinant is
$a_1 b_2 - b_1 a_2 = \operatorname{Im}(\bar\omega_1 \omega_2)$, and translation preserves Lebesgue
measure. For item 2, write $z - \alpha = s_1 \omega_1 + s_2 \omega_2$ with $s_1, s_2$ real; then
$z \in P + m_1 \omega_1 + m_2 \omega_2$ exactly when $m_k = \lfloor s_k \rfloor$ for $k = 1, 2$.

## Depends on

- [Fundamental parallelogram](fundamental-parallelogram.md)

## Proof depends on

- [Membership in a fundamental parallelogram](mem-fundamental-parallelogram-iff.md), for the
  description of $P$ by the coordinates $t_1, t_2 \in [0, 1)$
- [Coordinates in the period basis](basis-repr-omega.md), for the coordinates $s_1, s_2$ of a complex
  number in the basis $\omega_1, \omega_2$

## Sources

- J. H. Silverman, "Heights and elliptic curves", in G. Cornell and J. H. Silverman (eds.),
  *Arithmetic Geometry* (Storrs, 1984), Springer, New York, 1986, 253–265,
  <https://doi.org/10.1007/978-1-4613-8655-1_10>: p. 254, Remark 1.2 (4), $\operatorname{Im} \tau_v$ is
  the area of a fundamental parallelogram for $E/\bar K_v$; p. 256, the computation
  $\frac{i}{2} \int |\Delta(\tau)|^{1/6} dz \wedge d\bar z = |\Delta(\tau)|^{1/6} \int dx \wedge dy = |\Delta(\tau)|^{1/6} \operatorname{Im}(\tau)$,
  the last integral being the area of a fundamental parallelogram for
  $\mathbb{C}/(\mathbb{Z} + \mathbb{Z}\tau)$.
