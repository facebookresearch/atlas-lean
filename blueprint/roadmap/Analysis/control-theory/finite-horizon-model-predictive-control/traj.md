# State trajectory of a finite-horizon control problem

Let $f : X \to U \to X$ be discrete-time dynamics, $x_0 \in X$ an initial state and $u : \{0,\dots,N-1\} \to U$ a finite input sequence. The trajectory is defined for times $k \le N$ by

$$x_0(u) = x_0, \qquad x_{k+1}(u) = f(x_k(u), u_k) \quad (k < N).$$
