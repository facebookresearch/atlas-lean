# Bistability of cooperators in a public-good chemostat without cheaters

**Model.** With constant dilution rate $D > 0$ and inflow concentration $S_0 > 0$, a cooperator $X_1$
secretes an enzyme $E$ that converts unprocessed nutrient $S$ into processed nutrient $P$ at rate
$E\,G(S)$; it allocates a fraction $q \in (0, 1)$ of its uptake $\frac{1}{\gamma} F(P)$ to growth and $1 - q$ to
enzyme:

$$\dot{S} = D(S_0 - S) - E\,G(S), \quad \dot{P} = E\,G(S) - \tfrac{1}{\gamma} X_1 F(P) - D P, \quad
\dot{E} = (1 - q) X_1 F(P) - D E, \quad \dot{X}_1 = X_1 \bigl(q F(P) - D\bigr).$$

**Hypothesis (H1').** $G$ is $C^2$ with $G(0) = 0$, $G' > 0$ on $(0, \infty)$ and $G'' \le 0$; $F$ is $C^1$
with $F(0) = 0$ and $F' > 0$ on $(0, \infty)$ (Monod functions and linear $G$ qualify).

**Theorem.** Assume (H1') and $P^* := F^{-1}(D / q) < S_0$, where $P^*$ is the processed-nutrient level
at which cooperator growth balances dilution. Positive steady states correspond to the solutions of a
single scalar nonlinear equation, and:

1. if that equation has no solution, the washout state $(S_0, 0, 0, 0)$ (zero processed nutrient,
   enzyme and cooperators) is globally asymptotically stable;
2. if it has two distinct solutions, there are exactly two positive steady states $E_1$ and $E_2$
   besides washout; washout and $E_2$ are locally asymptotically stable, $E_1$ is a saddle with a
   three-dimensional stable manifold that separates the two basins, and every solution converges to
   one of the three steady states.

Hence cooperators persist from initial conditions in the basin of $E_2$ (or on the stable manifold of
$E_1$), and wash out from the rest: an Allee-type threshold created by the shared enzyme.

## Depends on

- [Obligate cheaters drive a public-good chemostat to washout](obligate-cheaters-drive-a-public-good-chemostat-to-washout.md)
- [Chemostat equilibria and the washout threshold](../../chemostat/chemostat-equilibria-and-washout.md)

## Expansion

At a positive steady state $q F(P) = D$ forces $P = P^*$, and the remaining balance equations reduce
to one equation for the substrate level; concavity of $G$ limits it to at most two roots. Washout is
always locally stable because, with no enzyme, no processed nutrient is available and a small
cooperator population cannot grow: cooperation pays only once enough enzyme has accumulated, which
is the source of bistability. Compared with the cheater theorem, the dynamics differ only in the
initial absence of the non-producing type, yet the long-run outcome changes from certain collapse to
possible persistence.

## Sources

- M. Schuster, E. Foxall, D. Finch, H. Smith, P. De Leenheer, "Tragedy of the commons in the
  chemostat", PLoS ONE 12 (2017) e0186119, Eqs. 12-15 and Theorem 2 (proof in S3 Appendix),
  <https://doi.org/10.1371/journal.pone.0186119> (PMC5737893).
