# Obligate cheaters drive a public-good chemostat to washout

**Model.** In a chemostat with dilution rate $D(t)$ and inflow concentration $S_0(t)$ of an unprocessed
nutrient $S$, an extracellular enzyme $E$ converts $S$ into a processed nutrient $P$ at rate $G(E, S)$. A
cooperator $X_1$ and an obligate cheater $X_2$ consume $P$ at the same per capita rate
$\frac{1}{\gamma} F(P)$ with the same yield $\gamma$; the cooperator puts a fraction $q \in (0, 1)$ of its
uptake into growth and $1 - q$ into enzyme, the cheater makes no enzyme:

$$\begin{aligned}
\dot{S} &= D(t)\bigl(S_0(t) - S\bigr) - G(E, S), &
\dot{P} &= G(E, S) - \tfrac{1}{\gamma}(X_1 + X_2) F(P) - D(t) P, \\
\dot{E} &= (1 - q) X_1 F(P) - D(t) E, &
\dot{X}_1 &= X_1 \bigl(q F(P) - D(t)\bigr), \qquad \dot{X}_2 = X_2 \bigl(F(P) - D(t)\bigr).
\end{aligned}$$

**Hypotheses.** (H1) $G$ and $F$ are $C^1$ and nonnegative with $G(0, S) = G(E, 0) = 0$ and $F(0) = 0$.
(H2) $D$ and $S_0$ are continuous, with $0 < \underline{D} \le D(t) \le \overline{D}$ and
$0 < \underline{S}_0 \le S_0(t) \le \overline{S}_0$ for all $t \ge 0$.

**Theorem (tragedy of the commons).** Under (H1) and (H2), if $X_2(0) > 0$ then

$$\bigl(P(t), E(t), X_1(t), X_2(t)\bigr) \to (0, 0, 0, 0) \quad (t \to \infty):$$

cheaters take over and the whole population, cheaters included, washes out. The conclusion persists
when the enzymatic step goes through intermediate enzyme-substrate complexes
$S + E \rightleftharpoons C \to P + E$ with mass-action rates.

## Depends on

- [Chemostat equilibria and the washout threshold](../../chemostat/chemostat-equilibria-and-washout.md)

## Expansion

The ratio $X_1 / X_2$ satisfies $\frac{d}{dt} \ln(X_1 / X_2) = -(1 - q) F(P) \le 0$, so cooperators
can only lose ground, and they lose it at a rate proportional to the resource they consume. Boundedness
comes from conservation of nutrient mass through the processing reaction and the bounded
operating conditions. If the
cooperator density stayed bounded away from zero, $F(P)$ would have to be persistently positive, and
then the ratio would decay to zero, a contradiction; once cooperators vanish, enzyme decays at rate at
least $\underline{D}$, processing stops, $P \to 0$, and the cheater, whose growth needs $P$, is diluted
out. No payoff matrix or Prisoner's Dilemma assumption is needed: the collapse follows from mass
balance alone.

## Sources

- M. Schuster, E. Foxall, D. Finch, H. Smith, P. De Leenheer, "Tragedy of the commons in the
  chemostat", PLoS ONE 12 (2017) e0186119, Eqs. 1-11 and Theorem 1 (proofs in S1 and S2 Appendices),
  <https://doi.org/10.1371/journal.pone.0186119> (PMC5737893).
