# A flow–reset–flow execution of a scalar hybrid automaton

Let $H$ have one mode $q$, continuous state $x \in \mathbb{R}$, vector field $f(q, x) = 1$, domain $\mathrm{Dom}(q) = \{x \le 1\}$, one edge $e = (q, q)$ with guard $G(e) = \{1\}$ and reset $R(e, 1) = \{0\}$, and $\mathrm{Init} = \{(q, 0)\}$. Let $\tau = ([0, 1], [1, 2])$, $x_0(t) = t$ on $[0, 1]$, $x_1(t) = t - 1$ on $[1, 2]$, and $q_0 = q_1 = q$. Then:

1. $(\tau, q, x)$ is a finite execution of $H$, with final state $(q, 1)$;
2. at the switching time the state is $1$ just before and $0$ just after the reset, and the elapsed time of the execution is $2$;
3. it is the only execution of $H$ with elapsed time $2$ and exactly one discrete transition: the flow is unique, the guard is met only at $x = 1$, and the domain forbids flowing past $x = 1$. (Executions with a further reset at time $2$, through an interval of length zero, also have elapsed time $2$.)

**Proof.** For part 1, $(q_0(0), x_0(0)) = (q, 0) \in \mathrm{Init}$; $x_0$ and $x_1$ solve $\dot x = 1$; $x_0(t) \le 1$ and $x_1(t) \le 1$ on the intervals; and $x_0(1) = 1 \in G(e)$ with $x_1(1) = 0 \in R(e, 1)$. Part 2 reads off $x_0(1)$ and $x_1(1)$. For part 3, a segment starting at $0$ at time $\tau_i$ is $t \mapsto t - \tau_i$ by uniqueness and has length at most $1$ because of the domain; the single discrete transition must start from $x = 1$, so the first segment has length exactly $1$, the reset gives $0$, and the second segment has the remaining length $1$.

## Depends on

- [Executions of a hybrid automaton](executions-of-a-hybrid-automaton.md): the conditions verified here

## Sources

- J. Lygeros, *Lecture Notes on Hybrid Systems*, ENSIETA, 2004, <https://people.eecs.berkeley.edu/~sastry/ee291e/lygeros.pdf>, Definitions 3.1 and 3.4 (hybrid automata and executions, pp. 21 and 25). The example is checked on the page.
