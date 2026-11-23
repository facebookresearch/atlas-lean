# Functional equation of the Epstein zeta function of a binary form

For $z = x + iy$ with $y > 0$, let

$$Z(z, s) = \sum_{(m, n) \neq (0, 0)} \frac{y^s}{|m + n z|^{2s}} \qquad (\operatorname{Re} s > 1)$$

be the Epstein zeta function of the binary quadratic form $Q_z(u, v) = y^{-1} |u + v z|^2$ of
determinant $1$, the sum running over the pairs of integers other than $(0, 0)$, and put
$\Lambda(z, s) = \pi^{-s} \Gamma(s) Z(z, s)$. Then $Z(z, s)$ continues to a meromorphic function of
$s \in \mathbb{C}$ whose only pole is a simple pole at $s = 1$, with residue $\pi$, and

$$\Lambda(z, s) = \Lambda(z, 1 - s).$$

In particular $\Lambda(z, s)$ has simple poles at $s = 1$ and $s = 0$, with residues $1$ and $-1$, and
$Z(z, 0) = -1$, since $\Gamma(s)$ has residue $1$ at $s = 0$.

This is Siegel's Theorem 3 for the form $Q = Q_z$ in $n = 2$ variables, with $|Q| = 1$, the spherical
function $P = 1$ of order $g = 0$ and $u = v = 0$: then $\zeta(s, 0, 0, Q, 1) = Z(z, s)$, and the dual
form $Q^{-1}[x] = y^{-1} |x_1 z - x_2|^2$ has the same zeta function, as the substitution
$(m_1, m_2) \mapsto (-m_2, m_1)$ shows (Siegel, p. 48). Siegel proves Theorem 3 by Riemann's method,
writing $\Lambda(z, s)$ through the Mellin transform of $\Theta(t) - 1$, where
$\Theta(t) = \sum_{m \in \mathbb{Z}^2} e^{-\pi t Q[m]}$ for $t > 0$, and using the transformation formula
$\Theta(t) = t^{-1} \sum_{m \in \mathbb{Z}^2} e^{-\pi Q^{-1}[m] / t}$ (Siegel, Proposition 7, for $|Q| = 1$). Siegel proves
Proposition 7 by induction on the number of variables from the one-variable theta transformation formula
$\sum_{n \in \mathbb{Z}} e^{-\pi \xi (n + v)^2} = \xi^{-1/2} \sum_{n \in \mathbb{Z}} e^{-\pi n^2 / \xi + 2\pi i n v}$, valid for complex
$v$ and $\operatorname{Re} \xi > 0$ with the branch of $\sqrt{\xi}$ that is positive for $\xi > 0$ (his formula (52)); for
the binary form $Q_z$ the two steps apply it in $m_1$ for fixed $m_2$, with the shift $m_2 x$, and then in $m_2$.

## Sources

- C. L. Siegel, *Lectures on advanced analytic number theory*, notes by S. Raghavan, Tata Institute of
  Fundamental Research Lectures on Mathematics 23, Bombay (1961, reissued 1965),
  <https://www.math.tifr.res.in/~publ/ln/tifr23.pdf> (copy:
  <https://www-users.cse.umn.edu/~garrett/m/mfms/notes_2013-14/Siegel_AdvAnNoTh.pdf>), Chapter 1: §4,
  formula (52) (p. 35); §5, Proposition 7 (p. 42), the functional equation (61) and Theorem 3 (p. 47),
  and their specialisation to binary forms on p. 48.
