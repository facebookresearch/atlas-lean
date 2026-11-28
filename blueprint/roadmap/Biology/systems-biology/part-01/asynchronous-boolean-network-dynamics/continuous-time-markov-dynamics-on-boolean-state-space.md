# Continuous-time Markov dynamics on a Boolean state space

**Setting.** A Boolean network has nodes $1, \dots, n$ and state space $\Sigma = \{0,1\}^n$. In asynchronous Boolean dynamics, each node $i$ has a logic $B_i : \Sigma \to \{0,1\}$, an asynchronous transition $S \to S'$ changes exactly one coordinate $j$ to $S'_j = B_j(S) \ne S_j$, and the discrete-time Markov chain moves to each of the $\gamma(S)$ available asynchronous successors with probability $1/\gamma(S)$.

**Continuous-time generalization.** Replace each logic $B_i$ by two nonnegative rate functions $R_i^{\mathrm{up}}, R_i^{\mathrm{down}} : \Sigma \to [0, \infty)$ and define a time-homogeneous continuous-time Markov chain on $\Sigma$ with rates

$$\rho(S \to S') = \begin{cases} R_i^{\mathrm{up}}(S) & \text{if } S, S' \text{ differ only at node } i \text{ and } S_i = 0,\\ R_i^{\mathrm{down}}(S) & \text{if } S, S' \text{ differ only at node } i \text{ and } S_i = 1,\\ 0 & \text{if } S, S' \text{ differ at more than one node.} \end{cases}$$

The instantaneous probabilities $P_t(S)$ solve the master equation $\dot P_t(S) = \sum_{S'} [\rho(S' \to S) P_t(S') - \rho(S \to S') P_t(S)]$. Choosing $R_i^{\mathrm{up}}(S) = B_i(S)$ and $R_i^{\mathrm{down}}(S) = 1 - B_i(S)$ makes the embedded jump chain $P(S \to S') = \rho(S \to S')/\sum_{S''}\rho(S \to S'')$ the asynchronous Boolean dynamics.

**Properties.** Since $\Sigma$ is finite:

1. $P_t$ converges as $t \to \infty$ to a stationary distribution, which is a convex combination of indecomposable stationary distributions; a cycle of the transition graph with no outgoing edges (more generally, a closed communicating class) supports an indecomposable stationary distribution.
2. Instantaneous probabilities cannot be exactly periodic. Damped oscillation (some $P_t(S)$ with infinitely many extrema) requires the transition-rate matrix to have a non-real eigenvalue, and when such an eigenvalue exists some initial condition produces damped oscillations. A non-real eigenvalue requires a cycle in the transition graph, but a cycle does not guarantee one.

**Simulation (Boolean kinetic Monte Carlo).** From state $S$ at time $t_0$, with independent uniforms $u, u' \in (0,1]$: let $\rho_{\mathrm{tot}} = \sum_{S'} \rho(S \to S')$; set $\delta t = -\log(u)/\rho_{\mathrm{tot}}$; order the successors $S'^{(1)}, S'^{(2)}, \dots$ with rates $\rho^{(j)}$ and move to $S'^{(k)}$ with $\sum_{j<k} \rho^{(j)} < u'\rho_{\mathrm{tot}} \le \sum_{j \le k} \rho^{(j)}$. Averaging indicator functions over independent trajectories estimates $P_t(S)$.

## Depends on

- [Gillespie direct method](../../gillespie-direct-method.md)

## Expansion

The construction keeps the qualitative wiring of a logical model but assigns each node separate activation and inactivation speeds, so relative timescales and priority rules (a rate set to zero) become parameters instead of ad hoc update orders. Convergence follows from finiteness of $\Sigma$: the generator $Q$ has $P_t = P_0 e^{tQ}$, and all non-zero eigenvalues of $Q$ have negative real part, so the limit exists and lies in the kernel of $Q^{\top}$, spanned by the stationary distributions of the closed classes. Oscillatory transients come from complex-conjugate eigenvalue pairs, whose contributions $e^{t\,\mathrm{Re}\lambda}\cos(t\,\mathrm{Im}\lambda)$ produce infinitely many extrema while decaying. Because $Q$ is $2^n \times 2^n$, matrix exponentials are infeasible for large $n$, which is why trajectory sampling by the Gillespie step is used.

## Sources

- G. Stoll, E. Viara, E. Barillot, L. Calzone, "Continuous time Boolean modeling for biological signaling: application of Gillespie algorithm", BMC Systems Biology 6 (2012) 116, Results: "Markov process for Boolean model", equations (4)–(6), "Asymptotic behavior of continuous time Markov process", "Oscillations and cycles", "BKMC", <https://doi.org/10.1186/1752-0509-6-116> (PMC3517402).
