# Uniqueness for the mean field game system

Let $T > 0$. Assume that $F$ and $G$ are bounded and Lipschitz on $\mathbb{R}^d \times P_1$,
with $P_1$ carrying the Kantorovich–Rubinstein distance $W_1$, and that $m_0$ is a Hölder
continuous probability density with finite second moment (the hypotheses of Cardaliaguet's
existence theorem 3.1). Assume the Lasry–Lions monotonicity conditions

$$\int (F(x, m_1) - F(x, m_2))\, d(m_1 - m_2)(x) > 0 \ \ (m_1 \ne m_2), \qquad \int (G(x, m_1) - G(x, m_2))\, d(m_1 - m_2)(x) \ge 0 .$$

Then two classical solutions of the [mean field game system](mean-field-game-system.md) with
bounded $u$ and bounded $Du$ coincide.

The proof, as in the [one-shot case](eq-of-is-mean-field-equilibrium.md), adds two inequalities:
test the Fokker–Planck equation for $m_1 - m_2$ with $u_1 - u_2$, test the Hamilton–Jacobi–Bellman
equation for $u_1 - u_2$ with $m_1 - m_2$, and integrate over $\mathbb{R}^d \times (0, T)$; the
[Lasry–Lions identity](lasry-lions-identity.md) turns the Hamiltonian terms into
$-\frac{m_1 + m_2}{2}|Du_1 - Du_2|^2 \le 0$, leaving $\int\!\!\int (m_1 - m_2)(F(x, m_1) - F(x, m_2)) \le 0$, so
$m_1 = m_2$, and then $u_1 = u_2$ since both solve the same Hamilton–Jacobi–Bellman equation.

The bounds on $u$ (on $[0, T]$) and on $Du$ (on $(0, T)$) are an extra hypothesis, not in the
statement of Theorem 3.6; they hold in the class where Theorem 3.1 constructs solutions
($|u| \le (1 + T) C_0$, $|Du| \le C_0$), and they justify the integrations by parts. With them the
statement is weaker than the source's. Solutions are only required to be $C^2$ in space
and $C^1$ in time for $0 < t < T$ and continuous up to the end points; the duality argument is
then run on $[\varepsilon, T - \varepsilon]$ and passed to the limit.

## Satisfiability

For $d \ge 1$ the hypotheses hold together, for example, with $F(x, m) = \int \rho(x - y)\, dm(y)$
for a Gaussian $\rho$, $G = 0$ and a Gaussian initial density $m_0$. Then $F$ is bounded, Lipschitz
in $x$ and $W_1$-Lipschitz in $m$ (Kantorovich–Rubinstein, $\rho$ being Lipschitz). Condition (17)
holds because $\iint \rho(x - y)\, d(m_1 - m_2)(x)\, d(m_1 - m_2)(y)$ is, up to a positive constant,
$\int \hat\rho\, |\hat m_1 - \hat m_2|^2 > 0$ for $m_1 \ne m_2$, since $\hat\rho > 0$. Condition (18) is
trivial, and Theorem 3.1 provides a classical solution with bounded $u$ and $Du$.

## Informally uses

- [The Lasry–Lions identity](lasry-lions-identity.md): the pointwise identity of the proof.

## Background

- [Wasserstein distances](../../../MeasureTheory/optimal-transport/wasserstein-distances/README.md):
  the distance $W_1$ in the Lipschitz hypothesis.

## Sources

- J.-M. Lasry and P.-L. Lions, "Mean field games", Japan. J. Math. 2 (2007), 229–260.
- P. Cardaliaguet, *Notes on Mean Field Games (from P.-L. Lions' lectures at Collège de France)*, version of 27 September 2013, assumptions 1–3 before Theorem 3.1, conditions (17)–(18) and Theorem 3.6.
