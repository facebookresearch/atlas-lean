# Mean field games

Lasry and Lions (2006–2007) model games with a continuum of identical, individually negligible players: each player optimises against the distribution $m$ of the others, and an equilibrium is a distribution reproduced by the players' best responses. In the one-shot version on a state space $Q$ with cost $F(y, m)$, an equilibrium is a distribution supported on the minimisers of $F(\cdot, m)$; the dynamic version is the mean field game system, a backward Hamilton–Jacobi–Bellman equation for the value of a typical player coupled with a forward Fokker–Planck equation for the distribution of players. Under the Lasry–Lions monotonicity condition $\int (F(y, m_1) - F(y, m_2))\, d(m_1 - m_2)(y) > 0$ for $m_1 \neq m_2$ (crowd aversion) the equilibrium is unique, in both versions, by the same duality argument.

This topic covers the one-shot equilibrium on a finite state space, its characterisation, the Lasry–Lions uniqueness theorem and existence, and the second-order mean field game system on $\mathbb{R}^d$ with its uniqueness theorem and the pointwise identity behind it.

- [Mean field equilibrium on a finite state space](is-mean-field-equilibrium.md)
- [Equilibria are supported on minimisers](is-mean-field-equilibrium-iff.md)
- [Lasry–Lions uniqueness of mean field equilibria](eq-of-is-mean-field-equilibrium.md)
- [Existence of mean field equilibria](exists-is-mean-field-equilibrium.md)
- [The mean field game system](mean-field-game-system.md)
- [The Lasry–Lions identity](lasry-lions-identity.md)
- [Uniqueness for the mean field game system](mean-field-game-system-uniqueness.md)
- [Points of the standard simplex are probability vectors](weights-is-prob.md)

## Related topics

- [Selfish routing and the price of anarchy](../selfish-routing-and-the-price-of-anarchy/README.md): Wardrop equilibria of nonatomic routing games are mean field equilibria, unique in latency by the same monotonicity argument.
- [Potential games](../potential-games/README.md): minimisers of an exact potential are Nash equilibria; likewise, when the mean field cost is the derivative of a potential in the distribution, minimisers of the potential are mean field equilibria (Cardaliaguet, §2.5).
- [Nash's theorem](../nash-s-theorem/README.md): mean field equilibria are limits of Nash equilibria of games with many players.
- [Viscosity solutions of Hamilton–Jacobi equations](../../../Analysis/partial-differential-equations/viscosity-solutions-of-hamilton-jacobi-equations/README.md): the Hamilton–Jacobi–Bellman half of the mean field game system.
- [Fokker–Planck equation](../../../Probability/stochastic-calculus/fokker-planck-equation/README.md): the Fokker–Planck half of the system.
- [Wasserstein distances](../../../MeasureTheory/optimal-transport/wasserstein-distances/README.md): the Kantorovich–Rubinstein distance on distributions used in the existence theory.
