# Approximate majority network and the cell-cycle switch

**Network.** Three species $x, y, b$ ($b$ the "undecided" state) with total count $N = x + y + b$ conserved, and the four catalytic reactions (mass action, common rate constant $k$)

$$x + y \to x + b, \qquad x + y \to y + b, \qquad x + b \to x + x, \qquad y + b \to y + y,$$

i.e. $x$ catalyses $y \to b \to x$ and $y$ catalyses $x \to b \to y$.

**Stochastic (population-protocol) behaviour.** Interpreting each reaction as a random pairwise interaction among $N$ agents:

1. *Fast:* with high probability the population reaches a single species after $O(N \log N)$ interactions, i.e. $O(\log N)$ parallel time; this is asymptotically optimal, since $\Omega(N \log N)$ interactions are needed for every agent to be influenced, directly or indirectly, by every other.
2. *Reliable:* if the initial margin satisfies $|x_0 - y_0| = \omega(\sqrt{N} \log N)$, the initial majority wins with high probability.
3. *Robust:* correctness persists when a subpopulation of order $o(\sqrt N)$ behaves arbitrarily (adversarially).

**Deterministic behaviour.** The mass-action ODE

$$\dot x = k\,x(b - y), \qquad \dot y = k\,y(b - x), \qquad \dot b = k\,(2xy - xb - yb)$$

on the simplex $x + y + b = N$ has stable equilibria $(N, 0, 0)$ and $(0, N, 0)$ and an interior equilibrium $x = y = b = N/3$, which is unstable: $\frac{d}{dt}(x - y) = k\,b\,(x - y)$, so any imbalance is amplified and the system switches to the initial majority.

**Transformation to the cell-cycle switch.** Replacing the mutual autocatalysis by catalysis through intermediate activators ($r$ activated by $x$ and activating $x$; $z$ activated by $y$ and activating $y$, with threshold catalysts) gives the *simply catalytic* switch with the same convergence up to a time factor. Removing the catalytic activity of $y$ and letting $x$ inactivate $y$ through $z$ yields the core **cell-cycle switch**, with $x, y$ the active and inactive forms of the cyclin-dependent kinase and $r, z$ the active forms of the phosphatase Cdc25 and the kinase Wee1; this network still computes approximate majority and implements an input-driven switch, and its performance matches AM when the extra feedback present in natural cell-cycle networks is included.

## Depends on

- [Chemical reaction network](../../../../Dynamics/smooth-dynamics/reaction-network.md)
- [Mass-action vector field](../../../../Dynamics/smooth-dynamics/mass-action-field.md)

## Expansion

The undecided state $b$ is what makes AM fast: a single $x$–$y$ encounter turns one agent undecided, and undecided agents are recruited by whichever species is more abundant, so the majority's lead grows multiplicatively, the same positive feedback visible in $\frac{d}{dt}(x - y) = k\,b\,(x - y)$. The deterministic picture captures only the bistable switching; the $O(\log N)$ time, the $\omega(\sqrt{N} \log N)$ reliability margin and robustness are statements about the stochastic kinetics (a continuous-time Markov chain on counts). The "pinched arrow" structure, where a catalyst drives a two-step conversion through an intermediate, is suggestive of multisite phosphorylation, which is how the transformed network maps onto Cdk regulation by Wee1 and Cdc25. The argument is that the cell-cycle switch is shaped by an algorithm (approximate majority) subject to biochemical constraints, not by chance.

## Sources

- L. Cardelli, A. Csikász-Nagy, "The cell cycle switch computes approximate majority", Scientific Reports 2 (2012) 656, Introduction and Results ("AM network", equation (1); transformations SC and CC; "AM and CC as isolated systems"), <https://doi.org/10.1038/srep00656>.
- D. Angluin, J. Aspnes, D. Eisenstat, "A simple population protocol for fast robust approximate majority", Distributed Computing 21 (2008) 87–102 (Theorems 1, 2 and 4), <https://doi.org/10.1007/s00446-008-0059-z>.
