# Noise-induced stabilization of a blow-up reaction network

**Setting.** Consider two species $S_1,S_2$ and the reaction network

$$3S_1+2S_2\to5S_1+S_2,\qquad 2S_1+3S_2\to S_1+5S_2,\qquad 4S_1\to\emptyset,\qquad 4S_2\to\emptyset,\qquad \emptyset\to S_1+S_2,$$

all with rate constant $1$. Under **stochastic mass-action kinetics** the molecule counts $X(t)=(X_1(t),X_2(t))\in\mathbb N^2$ form a continuous-time Markov chain with jump rates

$$q(x,x+2e_1-e_2)=x_1^{(3)}x_2^{(2)},\quad q(x,x-e_1+2e_2)=x_1^{(2)}x_2^{(3)},\quad q(x,x-4e_j)=x_j^{(4)},\quad q(x,x+e_1+e_2)=1,$$

where $y^{(p)}=y!/(y-p)!$ for $y\ge p$ and $0$ otherwise. Under **deterministic mass-action kinetics** the concentrations satisfy

$$\dot x_1=2x_1^3x_2^2-x_1^2x_2^3-4x_1^4+1,\qquad \dot x_2=-x_1^3x_2^2+2x_1^2x_2^3-4x_2^4+1 .$$

**Deterministic blow-up (Remark).** On the diagonal $x_1=x_2=f$ the ODE reduces to $\dot f=f^5-4f^4+1$, so every trajectory started at $(x,x)$ with $x>4$ diverges in finite time, while staying arbitrarily far from the boundary $\{x_1=0\}\cup\{x_2=0\}$ of the state space. Other choices of rate constants give the same behaviour along a ray $x_2=\beta x_1$.

**Theorem (positive recurrence).** The Markov chain $X(t)$ is positive recurrent; being irreducible, it has a unique stationary distribution.

## Expansion

The deterministic blow-up set is the diagonal, which is invariant but transversally unstable: off the diagonal, whichever species is in excess is converted into the other more slowly than it is degraded by the quartic decay, and the trajectory is pushed away from the diagonal towards regions where degradation dominates. In the stochastic system, intrinsic noise perturbs the state transversally to the diagonal before the polynomial growth along it can carry the process to infinity, so excursions along the unstable manifold are short and the process returns to a compact set. Unlike earlier examples of noise-induced stabilization, the mechanism does not rely on discreteness effects at the boundary of $\mathbb N^2$. The proof applies Filonov's criterion: with an energy function $V$ and suitable stopping times $\tau$, $\mathbb E_x[V(X(\tau))]-V(x)\le-\gamma\,\mathbb E_x[\tau]$ for all large $\|x\|_1$, verified separately inside a cone around the diagonal (using Gronwall-type control of the transverse fluctuation) and outside it. The excursions produce intermittent bursting in simulations.

## Sources

- A. Agazzi, L. Laurence, "Noise-induced stabilization in a chemical reaction network without boundary effects", arXiv preprint (2025), main theorem (Setup and main result), Proposition 1 (Filonov's criterion), Propositions 2 and 3, <https://doi.org/10.48550/arXiv.2506.12163>.
