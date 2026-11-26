# Unique delay equilibrium of the SI social-distancing game

**Game.** Time is scaled so that the baseline transmission rate is $1$ and the cost of infection is $1$; there is no discounting. The infected fraction follows $\dot I=\bar\sigma\,I(1-I)$, $I(0)=I_0\in(0,1]$, on $[0,t_f]$, where the population's average distancing spending $\bar c$ reduces transmission by $\bar\sigma=\sigma(\bar c)$ with threshold-linear efficiency
$$\sigma(c)=(1-mc)^+,\qquad m>0,$$
so spending at rate $1/m$ prevents infection completely. A susceptible individual spending $c(t)$ has infection hazard $\sigma(c)I$ and expected disutility equal to the probability of infection by $t_f$ plus expected accrued spending until infection or $t_f$.

**Necessary conditions (Section 5).** If $c^*$ is a subgame-perfect Nash equilibrium, then with the decision potential $\Phi$ solving $\dot\Phi=(1-mc^*)^+\Phi+c^*I$ backward from $\Phi(t_f)=I(t_f)$,
$$c^*\in\{0\}\ \text{if }\Phi<1/m,\qquad c^*\in[0,1/m]\ \text{if }\Phi=1/m,\qquad c^*\in\{1/m\}\ \text{if }\Phi>1/m.$$

**Theorem 6.** These necessary conditions have exactly one solution; hence the equilibrium is unique.

**Delay strategies.** Let $\xi(t;x)=\mathrm H(t-t_f+x)/m$ (no distancing, then maximal distancing during the final $x$ time units), $x\in[0,t_f]$, and let $\mathcal D(x,\bar x)$ be the disutility of an individual playing $x$ against a population playing $\bar x$; with $I(u)=I_0/[I_0+(1-I_0)e^{-u}]$ it is explicit.

**Theorem 12 (ESS).** Let $x^*\in(0,t_f)$ satisfy
$$I(t_f-x^*)=\frac{1}{m-x^*}.$$
Then for all $y\in[0,t_f]$, $y\ne x^*$: $\mathcal D(x^*,x^*)<\mathcal D(y,x^*)$ (strict Nash) and $\mathcal D(x^*,y)<\mathcal D(y,y)$ (invasion), so $x^*$ is an evolutionarily stable strategy.

**Theorem 11.** The delay game has no free-riding: $x^*$ also minimizes the population disutility $\mathcal E(\bar x)=\mathcal D(\bar x,\bar x)$.

## Expansion

Because $\sigma$ is linear below its threshold, the individual's optimal control problem is linear in $c$, so Pontryagin's principle gives a bang-bang switch governed by $\Phi$, the marginal value of remaining susceptible. Infection is permanent, so risk only rises toward $t_f$, which makes the switch happen once: no distancing early, full distancing for a terminal window of length $x^*$. The switching condition says that at time $t_f-x^*$ the instantaneous infection cost $I$ equals the cost $1/(m-x^*)$ of protecting for the rest of the game. Uniqueness comes from integrating the piecewise-constant system explicitly and showing the phase-plane trajectories of $(I,\Phi)$ cross the switching line $\Phi=1/m$ exactly once.

## Sources

- C. D. Olson, T. C. Reluga, "Social Distancing Equilibria in Games under Conventional SI Dynamics", arXiv preprint (2026), necessary conditions of Section 5, Theorem 6, Theorem 11 and Theorem 12, <https://doi.org/10.48550/arXiv.2603.12107>.
