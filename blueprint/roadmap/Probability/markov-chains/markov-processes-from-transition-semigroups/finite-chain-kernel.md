# Finite-dimensional kernel of a Markov semigroup at ordered times

Let $(K_t)_{t \ge 0}$ be a family of kernels on a measurable space $E$, $s \ge 0$ the time of the
starting state, and $\mathbf t = (t_0, \dots, t_{n-1})$ a list of requested absolute times
$t_i \ge 0$. The kernel $F_{s, \mathbf t}$ from $E$ to $E^n$ is defined by recursion on $n$: for
$n = 0$ it is the point mass at the empty vector, and

$$F_{s, (t_0, \dots, t_n)}(x, \cdot) = \text{law of } (y_0, y_1, \dots, y_n), \quad y_0 \sim K_{t_0 \mathbin{\dot{-}} s}(x, \cdot), \quad (y_1, \dots, y_n) \sim F_{t_0, (t_1, \dots, t_n)}(y_0, \cdot),$$

that is, $F_{s, (t_0, \dots, t_n)}(x, dy_0\, dy') = K_{t_0 \dot{-} s}(x, dy_0)\, F_{t_0, (t_1, \dots, t_n)}(y_0, dy')$,
where $a \mathbin{\dot{-}} b = \max(a - b, 0)$. If every $K_t$ is a Markov kernel, so is
$F_{s, \mathbf t}$. When moreover the $K_t$ form a Markov semigroup ($K_0$ the identity and the
Chapman–Kolmogorov equations $K_{s+t} = K_s K_t$) and $s \le t_0 \le t_1 \le \dots$, it is the law at the
times $t_0, \dots, t_{n-1}$ of the Markov process with transition kernels $K$ started at $x$ at time $s$;
repeated times then give equal coordinates. For an arbitrary family this reading fails: on
$E = \{0, 1\}$ with every $K_t(x, \cdot)$ uniform, the times $(0, 0)$ give the product of two uniform
laws, not the law of a pair $(X_0, X_0)$.
