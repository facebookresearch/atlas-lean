# Total-variation error of a finite-precision SSA step

This node collects error bounds for one step of the direct stochastic simulation algorithm when the
uniform random numbers come from a finite grid with $2^b$ points, $b \in \mathbb{N}$, and propensities are computed
approximately. The ideal step, from a state whose total propensity $a_0 = \sum_i a_i$ of the propensities
$a_1, \dots, a_R \ge 0$ is positive, draws independent $U_1, U_2$ uniform on $(0,1)$, sets the holding time $-\ln(U_1)/a_0$
and selects the least reaction $j$ with $a_1 + \dots + a_j > U_2 a_0$; states with $a_0 = 0$ are absorbing and take no
step.

## Expansion

A sound expansion has separate pages for:

1. **Endpoint-safe grids.** $U_2$ uniform on $\{0, 2^{-b}, \dots, 1 - 2^{-b}\}$ and $U_1$ uniform on
   $\{2^{-b}, \dots, 1\}$. A grid for $U_2$ that contains $1$ breaks the strict selection test (no
   reaction is selected at $U_2 = 1$), and a grid for $U_1$ that contains $0$ makes the holding time
   undefined.
2. **Reaction-choice error with exact propensities.** Each reaction's interval
   $\bigl[A_{j-1}/a_0,\ A_j/a_0\bigr)$, with $A_j = a_1 + \dots + a_j$, contains a number of grid points that
   differs from $2^b$ times its length by less than one, so the selection law differs from
   $(a_j/a_0)_j$ by less than $2^{-b}$ in each coordinate and by less than $R\,2^{-b}/2$ in total
   variation.
3. **Propensity error.** If each computed propensity satisfies $\lvert \hat a_i - a_i \rvert \le \eta a_i$
   with $0 \le \eta < 1$, the ideal selection laws for $\hat a$ and $a$ differ by at most
   $\eta/(1-\eta)$ in total variation.
4. **Holding time.** A discrete holding-time law is at total-variation distance $1$ from the
   exponential law, so its error must be stated for a coupling (for example a bound on
   $\lvert \hat\tau - \tau \rvert$ outside an event of small probability) or in a transport distance,
   not in total variation.
5. **Several steps.** Propagation of the per-step bounds over $n$ steps of the embedded jump chain,
   with the state-dependence of the propensities and the treatment of absorbing states made explicit.

## Depends on

- [Gillespie direct method (stochastic simulation algorithm)](gillespie-direct-method.md)

## Sources

- M. Giles, *Stochastic Simulation: Lecture 9* (chemical kinetics), University of Oxford.
  <https://people.maths.ox.ac.uk/gilesm/mc/stoch_sim/lec9.pdf> Background reference.
