# Total information processing capacity equals the number of state variables

**Setting.** A discrete-time dynamical system $x(t) = T(x(t-1), u(t))$ is driven by i.i.d. inputs $u(t) \in U$ with law $p(u)$, after a long initialization. Only $N$ state variables (or observation functions) $x_1(t), \dots, x_N(t)$ are accessible. For a target function $z$ of the last $h$ inputs, $z(t) = z(u(t-h+1), \dots, u(t))$, consider linear readouts $\hat z(t) = \sum_{i=1}^N W_i x_i(t)$ (no bias term) fitted on $T$ recorded steps.

**Definition 1 (capacity).**

$$C_T[X, z] = 1 - \frac{\min_W \langle (\hat z - z)^2\rangle_T}{\langle z^2\rangle_T},$$

where $\langle\cdot\rangle_T$ is the time average over the record; $C[X,z]$ is its limit as $T \to \infty$.

**Propositions 2–3.**

$$C_T[X, z] = \frac{\sum_{i,j}\langle z\,x_i\rangle_T\,\big(\langle x x^{\mathsf T}\rangle_T^{-1}\big)_{ij}\,\langle x_j\,z\rangle_T}{\langle z^2\rangle_T},$$

with the pseudo-inverse if $\langle x_ix_j\rangle_T$ is singular, and $0 \le C_T[X,z] \le 1$, with $C_T = 1$ iff $z$ is exactly a linear combination of the $x_i(t)$.

**Theorem 4 (capacity bound).** Let $y_1, \dots, y_L$ be orthogonal functions in $L^2(p^{\otimes h})$ with finite fourth moments. Then, as $T \to \infty$,

$$\sum_{l=1}^L C[X, y_l] \le N,$$

independently of $h$, $L$ and the chosen family.

**Theorem 7 (equality under fading memory).** Suppose the system has fading memory (each $x_i(t)$ is approximated arbitrarily well, uniformly in the initial state, by functions of the last $h$ inputs for large $h$, so that $x_i$ is an element of the Hilbert space of fading-memory functions of the input history), the $x_i$ and the target functions have finite fourth moments, and the correlation matrix $\mathbb{E}[x_ix_j]$ has rank $N$. If $Y_L = \{y_1, \dots, y_L\}$ is an increasing family of orthogonal functions that becomes a complete orthogonal system of that Hilbert space as $L \to \infty$, then

$$\lim_{L\to\infty}\sum_{l=1}^L C[X, y_l] = N .$$

## Expansion

In the limit, $C[X, z]$ is the squared norm of the orthogonal projection of $z/\|z\|$ onto the $N$-dimensional span of $x_1, \dots, x_N$ in $L^2$. For an orthonormal family $\{y_l\}$ the sum of the squared projections is the squared Hilbert–Schmidt norm of the projection restricted to their span, which is at most the rank $N$; completeness of the family and linear independence of the $x_i$ make it exactly $N$. Hence every fading-memory system with $N$ linearly independent observed variables has the same total capacity: different systems differ only in how they distribute it over memory of past inputs (linear functions of delayed inputs) and nonlinear computation (higher-degree polynomials, e.g. products of Legendre polynomials for uniform inputs), which exposes a memory–nonlinearity trade-off; noise reduces the total below $N$.

## Sources

- J. Dambre, D. Verstraeten, B. Schrauwen and S. Massar, "Information processing capacity of dynamical systems", Scientific Reports 2 (2012) 514, Definitions 1, 5–6, Propositions 2–3 and Theorems 4, 7, <https://doi.org/10.1038/srep00514>, PMCID PMC3400147.
