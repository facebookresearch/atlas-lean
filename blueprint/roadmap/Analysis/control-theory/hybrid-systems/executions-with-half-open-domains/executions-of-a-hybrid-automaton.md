# Executions of a hybrid automaton

A **hybrid automaton** $H = (Q, X, f, \mathrm{Init}, \mathrm{Dom}, E, G, R)$ consists of a set $Q$ of discrete states (modes), the continuous state space $X = \mathbb{R}^n$, a vector field $f : Q \times X \to \mathbb{R}^n$, a set $\mathrm{Init} \subseteq Q \times X$ of initial states, a domain $\mathrm{Dom}(q) \subseteq X$ for each mode, a set $E \subseteq Q \times Q$ of edges, a guard $G(e) \subseteq X$ for each edge and a reset map $R(e, x) \subseteq X$ for each edge and state. Its states are the pairs $(q, x) \in Q \times X$; $f(q, \cdot)$ is assumed locally Lipschitz for each $q$.

A **hybrid time set** is a finite or infinite sequence $\tau = (I_i)_{i=0}^N$ of intervals with $I_i = [\tau_i, \tau'_i]$ for $i < N$, with $I_N$ either $[\tau_N, \tau'_N]$ or $[\tau_N, \tau'_N)$ when $N < \infty$, and with $\tau_i \le \tau'_i = \tau_{i+1}$ for all $i$; intervals of length zero are allowed, so several discrete transitions can happen at the same instant. A **hybrid trajectory** $(\tau, q, x)$ assigns to each interval $I_i$ functions $q_i : I_i \to Q$ and $x_i : I_i \to X$.

An **execution** of $H$ is a hybrid trajectory such that

1. **initial condition:** $(q_0(\tau_0), x_0(\tau_0)) \in \mathrm{Init}$;
2. **discrete evolution:** for every $i$ with $i + 1 \le N$, $e_i = (q_i(\tau'_i), q_{i+1}(\tau_{i+1})) \in E$, $x_i(\tau'_i) \in G(e_i)$ and $x_{i+1}(\tau_{i+1}) \in R(e_i, x_i(\tau'_i))$;
3. **continuous evolution:** for every $i$, $q_i$ is constant on $I_i$, $x_i$ solves $\dot x = f(q_i, x)$ on $I_i$, and $x_i(t) \in \mathrm{Dom}(q_i)$ for every $t \in [\tau_i, \tau'_i)$.

The domain is required only on the half-open interval $[\tau_i, \tau'_i)$: the state may leave the domain exactly at the instant of a discrete transition. An execution is **finite** if $\tau$ is a finite sequence whose last interval is closed; its **final state** is $(q_N(\tau'_N), x_N(\tau'_N))$. A state is **reachable** if it is the final state of some finite execution.

## Background

- [Hybrid automata and their executions](../hybrid-automata-and-their-executions.md): the same notion with location invariants required on closed intervals, and reachability through the timed transition system

## Sources

- J. Lygeros, *Lecture Notes on Hybrid Systems*, ENSIETA, 2004, <https://people.eecs.berkeley.edu/~sastry/ee291e/lygeros.pdf>, Definition 3.1 (hybrid automaton, p. 21), Definition 3.2 (hybrid time set, p. 23), Definitions 3.3 and 3.4 (hybrid trajectory and execution, with the domain condition on $[\tau_i, \tau'_i)$, p. 25), Definition 3.5 (finite executions, p. 26) and Definition 4.1 (reachable states, p. 29).
