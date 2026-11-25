# Functional equation of the Epstein zeta function of a binary form

For $z = x + iy$ with $y > 0$, let

$$Z(z, s) = \sum_{(m, n) \neq (0, 0)} \frac{y^s}{|m + n z|^{2s}} \qquad (\operatorname{Re} s > 1)$$

be the Epstein zeta function of the binary quadratic form $Q_z(u, v) = y^{-1} |u + v z|^2$ of
determinant $1$, the sum running over the pairs of integers other than $(0, 0)$, and put
$\Lambda(z, s) = \pi^{-s} \Gamma(s) Z(z, s)$. Then $Z(z, s)$ continues to a meromorphic function of
$s \in \mathbb{C}$ whose only pole is a simple pole at $s = 1$, with residue $\pi$, and

$$\Lambda(z, s) = \Lambda(z, 1 - s).$$

In particular $\Lambda(z, s)$ has simple poles at $s = 1$ and $s = 0$, with residues $1$ and $-1$, and
$Z(z, 0) = -1$, since the [recurrence](../../../Analysis/special-functions/gamma-function/gamma-function-recurrence.md)
$\Gamma(s) = \Gamma(s + 1)/s$, with $\Gamma(1) = \int_0^\infty e^{-t} \, dt = 1$ and $\Gamma$
[analytic](../../../Analysis/special-functions/gamma-function/digamma-and-trigamma-functions/analytic-at-gamma.md) at $1$, gives $\Gamma$ the
residue $1$ at $s = 0$.

This is Siegel's Theorem 3 for the form $Q = Q_z$ in $n = 2$ variables, with $|Q| = 1$, the spherical
function $P = 1$ of order $g = 0$ and $u = v = 0$: then $\zeta(s, 0, 0, Q, 1) = Z(z, s)$, and the dual
form $Q^{-1}[x] = y^{-1} |x_1 z - x_2|^2$ has the same zeta function, as the substitution
$(m_1, m_2) \mapsto (-m_2, m_1)$ shows (Siegel, p. 48). Siegel proves Theorem 3 by Riemann's method: by Euler's
integral $\Gamma(s) = \int_0^\infty t^{s-1} e^{-t} \, dt$, applied term by term for $\operatorname{Re} s > 1$,
$\Lambda(z, s) = \int_0^\infty (\Theta(t) - 1) \, t^{s} \, \frac{dt}{t}$ with $\Theta(t) = \sum_{m \in \mathbb{Z}^2} e^{-\pi t Q[m]}$
for $t > 0$, and the transformation formula $\Theta(t) = t^{-1} \sum_{m \in \mathbb{Z}^2} e^{-\pi Q^{-1}[m] / t}$ (Siegel,
Proposition 7, for $|Q| = 1$) gives the continuation and the functional equation of $\Lambda$ (his (59)–(61)).
Siegel proves Proposition 7 by induction on the number of variables from the one-variable formula
$\sum_{n \in \mathbb{Z}} e^{-\pi \xi (n + v)^2} = \xi^{-1/2} \sum_{n \in \mathbb{Z}} e^{-\pi n^2 / \xi + 2\pi i n v}$, valid for complex
$v$ and $\operatorname{Re} \xi > 0$ with the branch of $\sqrt{\xi}$ that is positive for $\xi > 0$ (his formula (52)), which is the
[theta transformation of a Gaussian sum with a linear term](../../../Analysis/harmonic-analysis/fourier-series/gaussian-sum-with-linear-term-transformation.md) for $a = \xi$ and
$b = -\xi v$, multiplied by $e^{-\pi \xi v^2}$. For the binary form, completing the square gives
$Q_z(m_1, m_2) = y^{-1} \bigl( (m_1 + m_2 x)^2 + m_2^2 y^2 \bigr)$, so the first step applies the formula in $m_1$ for
fixed $m_2$, with the shift $v = m_2 x = m_2 \operatorname{Re} z$, and the second applies it in $m_2$. Finally
$Z(z, s) = \pi^s \Lambda(z, s) / \Gamma(s)$ has no poles other than those of $\Lambda$ except where $\Gamma$ vanishes, and
[$\Gamma$ has no zeros](../../../Analysis/special-functions/gamma-function/gamma-function-no-zeros.md), while its poles at $0, -1, -2, \dots$ only cancel poles of
$\Lambda$ or give zeros of $Z$; so the only pole of $Z(z, s)$ is the one at $s = 1$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Theta transformation of a Gaussian sum with a linear term](../../../Analysis/harmonic-analysis/fourier-series/gaussian-sum-with-linear-term-transformation.md), for the one-variable steps of Proposition 7, with the shift $m_2 \operatorname{Re} z$
- [The complex gamma function has no zeros away from its poles](../../../Analysis/special-functions/gamma-function/gamma-function-no-zeros.md), for passing from $\Lambda(z, s)$ to $Z(z, s)$ without further poles
- [Recurrence of the gamma function](../../../Analysis/special-functions/gamma-function/gamma-function-recurrence.md), for $\Gamma(s) = \Gamma(s + 1)/s$ and the residue of $\Gamma$ at $0$
- [Analyticity of the Gamma function](../../../Analysis/special-functions/gamma-function/digamma-and-trigamma-functions/analytic-at-gamma.md), for the continuity of $\Gamma$ at $1$

## Sources

- C. L. Siegel, *Lectures on advanced analytic number theory*, notes by S. Raghavan, Tata Institute of
  Fundamental Research Lectures on Mathematics 23, Bombay (1961, reissued 1965),
  <https://www.math.tifr.res.in/~publ/ln/tifr23.pdf> (copy:
  <https://www-users.cse.umn.edu/~garrett/m/mfms/notes_2013-14/Siegel_AdvAnNoTh.pdf>), Chapter 1: §4,
  formula (52) (p. 35); §5, Proposition 7 (p. 42), the termwise Euler integral (59) (p. 45), the continuation (60) and
  the functional equation (61) with Theorem 3 (p. 47), and their specialisation to binary forms on p. 48.
