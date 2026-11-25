# Value of a Markov policy

The value of a Markov policy $\pi$ is the limit, as $N \to \infty$, of its [N-stage values](n-stage-value.md) with terminal value $0$ (an unspecified function when this limit does not exist). For a finite MDP with stochastic transitions and $0 \le \gamma < 1$ the limit exists, and every terminal value gives the same limit ([The N-stage values of a Markov policy converge](tendsto-n-stage-value.md)).

Bertsekas defines the infinite-horizon cost of a policy as a $\limsup$ of its $N$-stage costs, for generality; under the contraction assumption the limit exists, so the two definitions agree here.

## Sources

- D. P. Bertsekas, *Abstract Dynamic Programming*, 3rd ed., Athena Scientific (2022), Section 1.2.1 (the infinite-horizon cost function $J_\pi$).
