# Feasible input sequences of a finite-horizon problem

Let $f : X \to U \to X$ be discrete-time dynamics with initial state $x_0$, let $U_s \subseteq U$ be the input constraint set, $X_s \subseteq X$ the state constraint set and $X_f \subseteq X$ the terminal set, and let $N \in \mathbb{N}$ be the horizon. An input sequence $u : \{0,\dots,N-1\} \to U$ with trajectory $x_k = x_k(u)$ is feasible when

- every input lies in the input set: $u_k \in U_s$ for all $k < N$;
- every state before the horizon, including $x_0$, lies in the state set: $x_k \in X_s$ for all $k < N$;
- the terminal state lies in the terminal set: $x_N \in X_f$.
