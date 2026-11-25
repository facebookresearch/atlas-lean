# Inductive invariants of a hybrid automaton contain its reachable states

Let $H = (Q, X, f, \mathrm{Init}, \mathrm{Dom}, E, G, R)$ be a hybrid automaton and $M \subseteq Q \times X$. Suppose that

1. **initiation:** $\mathrm{Init} \subseteq M$;
2. **flow closure:** whenever $(q, x) \in M$, $T \ge 0$, $\phi$ solves $\dot\phi = f(q, \phi)$ with $\phi(0) = x$ and $\phi(t) \in \mathrm{Dom}(q)$ for $t \in [0, T)$, then $(q, \phi(t)) \in M$ for all $t \in [0, T]$;
3. **jump closure:** whenever $(q, x) \in M$, $e = (q, q') \in E$ and $x \in G(e)$, then $\{q'\} \times R(e, x) \subseteq M$.

Then every execution $(\tau, q, x)$ of $H$ satisfies $(q_i(t), x_i(t)) \in M$ for every interval $I_i$ of $\tau$ and every $t \in I_i$. In particular every reachable state lies in $M$, and if $M \subseteq F$ for a set $F$ of safe states, then $H$ never leaves $F$.

**Proof.** By induction on $i$ show that $(q_i(\tau_i), x_i(\tau_i)) \in M$ and then that the whole segment lies in $M$. For $i = 0$ the starting state is in $\mathrm{Init} \subseteq M$. If the segment $i$ starts in $M$, the continuous evolution condition says that $x_i$ solves $\dot x = f(q_i, x)$ and stays in $\mathrm{Dom}(q_i)$ on $[\tau_i, \tau'_i)$, so flow closure, applied with $T = \tau'_i - \tau_i$ (or along every $T < \tau'_N - \tau_N$ for a final half-open interval), keeps the segment in $M$, including its right endpoint. The discrete evolution condition and jump closure then put the start of segment $i + 1$ in $M$. Reachable states are endpoints of finite executions.

## Depends on

- [Executions of a hybrid automaton](executions-of-a-hybrid-automaton.md): executions and reachable states

## Sources

- J. Lygeros, *Lecture Notes on Hybrid Systems*, ENSIETA, 2004, <https://people.eecs.berkeley.edu/~sastry/ee291e/lygeros.pdf>, Proposition 5.1 (a safety specification holds if and only if the reachable set lies in the safe set), Definition 5.1 and Proposition 5.2 (invariant sets containing the initial states contain the reachable set), and the inductive procedure checking initial states, continuous evolution in the domain and discrete transitions (pp. 39–40). The induction is written out on the page.
