# With closed domains, an execution stays in its domain at each switching time

Let $(\tau, q, x)$ be an execution of a hybrid automaton $H$, so that each continuous segment satisfies $x_i(t) \in \mathrm{Dom}(q_i)$ for $t \in [\tau_i, \tau'_i)$.

1. **Closed domains.** If $\mathrm{Dom}(q_i)$ is closed, $\tau_i < \tau'_i$ and the interval $I_i = [\tau_i, \tau'_i]$ is closed, that is, $I_i$ is not a half-open final interval $[\tau_N, \tau'_N)$, then $x_i(\tau'_i) \in \mathrm{Dom}(q_i)$: the segment satisfies the domain condition on the whole closed interval $[\tau_i, \tau'_i]$.
2. **Zero-length segments.** If $\tau_i = \tau'_i$, the half-open condition is vacuous, and the closed condition $x_i(\tau_i) \in \mathrm{Dom}(q_i)$ can fail even for a closed domain: a reset may land outside $\mathrm{Dom}(q_{i+1})$ provided another discrete transition follows at the same instant.
3. **Open domains.** Without closedness, part 1 fails: for one mode with $f = 1$, $\mathrm{Dom} = \{x < 1\}$, a self-loop with guard $\{1\}$ and reset $\{0\}$, and $\mathrm{Init} = \{(q, 0)\}$, the segment $x_0(t) = t$ on $[0, 1]$ is part of an execution, and $x_0(1) = 1 \notin \mathrm{Dom}$.

So the half-open and the closed formulations of the domain condition give the same executions without zero-length segments whenever every domain is closed, and they differ in general.

**Proof.** In part 1, $x_i$ is continuous and $x_i(t) \in \mathrm{Dom}(q_i)$ for $t < \tau'_i$ arbitrarily close to $\tau'_i$, so the limit $x_i(\tau'_i)$ lies in the closed set $\mathrm{Dom}(q_i)$. Part 2 is the definition with $[\tau_i, \tau_i) = \varnothing$. In part 3 the conditions of an execution hold: $x_0(t) = t < 1$ on $[0, 1)$, $x_0(1) = 1$ is in the guard, and the reset $0$ starts the next segment.

## Depends on

- [Executions of a hybrid automaton](executions-of-a-hybrid-automaton.md): the half-open domain condition

## Sources

- J. Lygeros, *Lecture Notes on Hybrid Systems*, ENSIETA, 2004, <https://people.eecs.berkeley.edu/~sastry/ee291e/lygeros.pdf>, Definition 3.4 (the domain condition is imposed for $t \in [\tau_i, \tau'_i)$, p. 25), and the transition system of a hybrid automaton, whose continuous transitions require the domain on the closed interval $[0, T]$ (pp. 42–43). The comparison of the two conventions is derived on the page.
