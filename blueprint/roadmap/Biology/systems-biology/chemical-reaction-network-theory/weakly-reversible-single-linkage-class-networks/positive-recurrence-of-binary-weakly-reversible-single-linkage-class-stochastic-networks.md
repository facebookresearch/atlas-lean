# Positive recurrence of binary weakly reversible single-linkage-class stochastic networks

**Setting.** A stochastic mass action system $(\mathscr{S},\mathscr{C},\mathscr{R},\kappa)$ is the continuous-time Markov chain $X$ on $\mathbb{Z}^N_{\ge0}$ that jumps by $y'-y$ at rate $\kappa_{y\to y'}\prod_i\frac{x_i!}{(x_i-y_i)!}\mathbf{1}_{x\ge y}$. The network is *binary* if every complex has total molecularity at most $2$ ($\|y\|_1\le2$). Weak reversibility and a single linkage class are as in the deterministic theory, which guarantees bounded and persistent deterministic trajectories.

**Statements.**
1. *(Main theorem.)* If $(\mathscr{S},\mathscr{C},\mathscr{R},\kappa)$ is weakly reversible, binary and has a single linkage class, and for every species $S$ at least one of $S$, $2S$ is a complex, then $X$ is positive recurrent on each closed communicating class.
2. *(Tier criterion.)* More generally, a weakly reversible single-linkage-class stochastic mass action system is positive recurrent if, along every proper tier sequence $\{z_n\}$ of states, the top tier of the stochastic (falling-factorial) intensities is contained in the top tier of the deterministic monomials, $T^{S,1}_{\{z_n\}}\subset T^{D,1}_{\{z_n\}}$.
3. *(Embedded chains.)* If the total jump intensity $\bar\lambda$ is bounded below on a closed class and the embedded discrete-time chain restricted to it is positive recurrent, then $X$ is non-explosive and positive recurrent there.

## Depends on

- [Bounded trajectories of weakly reversible single-linkage-class mass action systems](bounded-trajectories-of-weakly-reversible-single-linkage-class-mass-action-systems.md)

## Expansion

The deterministic boundedness proof finds, along any escaping sequence, a conservation-type function that the dominant reactions decrease. In the stochastic setting this function serves as a Lyapunov function, but one step of the jump chain only sees a single reaction, so the argument studies the $n$-step embedded chain, over which the dominant top-tier reactions have fired with high probability and produce a uniform negative drift outside a finite set (Foster's criterion). Falling factorials can differ from monomials when some counts are small, which is where the tier inclusion is needed; for binary networks with each species appearing as $S$ or $2S$, the inclusion holds, giving the main theorem.

## Sources

- David F. Anderson, Daniele Cappelletti and Jinsu Kim, "Stochastically modeled weakly reversible reaction networks with a single linkage class", Journal of Applied Probability 57 (2020), 792–810, <https://doi.org/10.1017/jpr.2020.28>; numbering as in arXiv:1904.08967: Theorems 3.1, 4.1 and 6.1.
