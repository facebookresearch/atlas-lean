# Discrete-time dynamical system (input-driven state-update map)

A discrete-time dynamical system is a triple $(X, U, f)$ with a state set $X$, an input set $U$ and an update map
$f : X \times U \to X$. Its trajectory from $x_0$ under an input word $u_0 u_1 \cdots$ is $x_{k+1} = f(x_k, u_k)$. An autonomous
system has a one-element input set. A nondeterministic system replaces $f$ by a successor relation
$\mathrm{Post} : X \times U \to 2^X$, and its trajectories are the sequences with $x_{k+1} \in \mathrm{Post}(x_k, u_k)$. An optional
observation map $h : X \to Y$ gives outputs $y_k = h(x_k)$. No metric, measure or real structure is assumed.

## Sources

- Planning Algorithms, Sec. 1.5 Organization of the Book — S. M. LaValle, Planning Algorithms. <http://msl.cs.uiuc.edu/~lavalle/planning/node34.html> Background reference.
