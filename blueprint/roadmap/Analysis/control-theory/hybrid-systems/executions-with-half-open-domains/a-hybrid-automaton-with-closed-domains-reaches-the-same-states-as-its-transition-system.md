# A hybrid automaton with closed domains reaches the same states as its transition system

Let $H = (Q, X, f, \mathrm{Init}, \mathrm{Dom}, E, G, R)$ be a hybrid automaton with every $\mathrm{Dom}(q)$ closed. Its **transition system** has states $Q \times X$, initial states $\mathrm{Init}$, and transitions $s \to s'$ of two kinds:

- a **discrete transition** $(q, x) \to (q', x')$ when $e = (q, q') \in E$, $x \in G(e)$ and $x' \in R(e, x)$;
- a **continuous transition** $(q, x) \to (q, \phi(T))$ when $T \ge 0$, $\phi$ solves $\dot\phi = f(q, \phi)$ with $\phi(0) = x$, and $\phi(t) \in \mathrm{Dom}(q)$ for every $t \in [0, T]$.

Then a state is reachable by $H$, that is, it is the final state of a finite execution, if and only if it is reached from an initial state by a finite sequence of transitions of the transition system.

**Proof.** Let $(\tau, q, x)$ be a finite execution with intervals $I_0, \dots, I_N$. Each segment of positive length is a continuous transition from $(q_i, x_i(\tau_i))$ to $(q_i, x_i(\tau'_i))$ of duration $\tau'_i - \tau_i$, since by the closedness of the domains it satisfies the domain condition on the closed interval; each passage from $I_i$ to $I_{i+1}$ is a discrete transition; and segments of length zero contribute nothing, their state being both the target of one discrete transition and the source of the next or the final state. Conversely, given a finite sequence of transitions from an initial state, drop the continuous transitions of duration $0$, merge consecutive continuous transitions into one segment by the semigroup property of the flow, give each remaining continuous transition an interval of its duration placed after the previous ones, insert an interval of length zero before every discrete transition that is not preceded by a continuous one, and end with an interval of length zero at the final state if the sequence is empty or ends with a discrete transition. The result is a finite execution with the same final state: the discrete evolution condition holds by the definition of discrete transitions, and the half-open domain condition follows from the closed one.

## Depends on

- [Executions of a hybrid automaton](executions-of-a-hybrid-automaton.md): executions, finite executions and reachable states

## Proof depends on

- [With closed domains, an execution stays in its domain at each switching time](with-closed-domains-an-execution-stays-in-its-domain-at-each-switching-time.md): segments of positive length satisfy the closed domain condition

## Sources

- J. Lygeros, *Lecture Notes on Hybrid Systems*, ENSIETA, 2004, <https://people.eecs.berkeley.edu/~sastry/ee291e/lygeros.pdf>, Definition 6.1 (transition systems, p. 41) and the transition system of a hybrid automaton, with discrete transition relations $\delta_e$ and the continuous relation $\delta_C$ requiring $x(t) \in \mathrm{Dom}(\hat q)$ for $t \in [0, T]$ (pp. 42–43), and Definition 4.1 (reachable states, p. 29). The correspondence between finite executions and paths of the transition system is proved on the page.
