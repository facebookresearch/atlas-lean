# Rate-to-probability error of synchronous contagion updates

**Continuous-time model.** In SIS dynamics on a network of $N$ nodes, a susceptible node is infected by each infected neighbour at rate $\beta$ and an infected node recovers at rate $\mu$; node $i$ flips state at rate $r_i = \beta m_{i,t}$ if susceptible ($m_{i,t}$ infected neighbours) and $r_i = \mu$ if infected. The network state $Y_t \in \{S, I\}^N$ is a continuous-time Markov chain with master equation

$$\frac{d}{dt} p(y, t) = \sum_{y' \neq y} \big( p(y', t)\, r_{y' \to y} - p(y, t)\, r_{y \to y'} \big).$$

On the complete graph it lumps exactly to the number of infected nodes $n \in \{0, \dots, N\}$:

$$\frac{d}{dt} p(n,t) = -\big(\mu n + \beta n (N-n)\big) p(n,t) + \mu (n+1)\, p(n+1, t) + \beta (n-1)(N - n + 1)\, p(n-1, t).$$

**Discrete-time approximation.** With time step $\Delta t$, rates are replaced by probabilities $\tilde\mu = \mu\Delta t$ and $\tilde\beta = \beta\Delta t$ (per infected neighbour), and all nodes update simultaneously from the state at the start of the step; this process obeys its own discrete master equation $p(y, t+1) = \sum_{y'} p(y', t)\, q_{y' \to y}$.

**Proposition.** For a single event of rate $\lambda > 0$, the exact probability that it occurs in a time window $\Delta t$ (in isolation) is $1 - e^{-\lambda\Delta t}$, and the discrete-time probability $\tilde\lambda = \lambda\Delta t$ overstates it by

$$\varepsilon(\tilde\lambda) = \tilde\lambda - \big(1 - e^{-\tilde\lambda}\big), \qquad 0 \le \varepsilon(\tilde\lambda) \le \frac{\tilde\lambda^2}{2},$$

so the per-step error is second order in $\tilde\lambda$; numerically $\varepsilon(0.1) \approx 0.005$, $\varepsilon(0.5) \approx 0.107$ and $\varepsilon(1) = e^{-1} \approx 0.37$. Moreover, synchronous updating ignores the change in neighbours' rates caused by state changes within a step. Consequently the discrete-time process converges to the continuous one only as $\tilde\beta, \tilde\mu \to 0$, and with $\Delta t = 1$ its behaviour depends on $\tilde\beta$ and $\tilde\mu$ separately rather than only on the effective rate $\gamma = \beta/\mu = \tilde\beta/\tilde\mu$.

## Expansion

The waiting time to an event of rate $\lambda$ is exponential, so $\Pr(\text{event in } [t, t+\Delta t]) = 1 - e^{-\lambda\Delta t}$. Taylor's theorem with $e^{-x} \ge 1 - x$ and $e^{-x} \le 1 - x + x^2/2$ for $x \ge 0$ gives $0 \le x - 1 + e^{-x} \le x^2/2$. The bound also shows why the discrete probability must be capped: $\tilde\lambda > 1$ is not a probability at all, so the range of rates studied with unit steps is restricted. Comparison of synchronous-update simulations with the exact lumped master equation on complete graphs shows accurate prevalence curves for $\tilde\lambda \lesssim 10^{-2}$ and visible errors once $\tilde\lambda \sim 10^{-1}$. On an Erdős–Rényi network with $N = 10^4$ and mean degree $4$, the simulated epidemic threshold (in $\gamma$) is $0.25$, the steady-state prediction, when $\tilde\mu = 0.1$ but falls to about $0.2$ when $\tilde\mu = 1$. Steady-state thresholds of discrete-time mean-field equations are unaffected; only quantities obtained by iterating or simulating the discrete dynamics are biased.

## Sources

- P. G. Fennell, S. Melnik and J. P. Gleeson, "Limitations of discrete-time approaches to continuous-time contagion dynamics", Physical Review E 94 (2016), 052125, Sections II–V (Eqs. (1)–(9), Figs. 2 and 5), <https://doi.org/10.1103/PhysRevE.94.052125>, PMCID: PMC7217503.
