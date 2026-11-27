# Convergence of an ODE switched by a Markov environment under average contraction

**Setting.** Let $(I_t)_{t \ge 0}$ be an irreducible continuous-time Markov chain on a finite set $F$ of environments, with invariant probability $\nu$. Given smooth vector fields $F^{(i)} : \mathbb{R}^d \to \mathbb{R}^d$, $i \in F$, the state $X_t \in \mathbb{R}^d$ follows

$$\partial_t X_t = F^{(I_t)}(X_t),$$

i.e. between jumps of the environment it moves along the flow of the current vector field. The pair $(X_t, I_t)$ is a piecewise deterministic Markov process (PDMP); in population dynamics $X_t$ is a vector of population sizes or traits in a randomly fluctuating environment. Assume each field is **contracting at rate** $\rho(i) \in \mathbb{R}$ (possibly negative):

$$\langle x - y, F^{(i)}(x) - F^{(i)}(y)\rangle \le -\rho(i)\,\|x - y\|^2 \qquad \text{for all } x, y \in \mathbb{R}^d .$$

(For $C^1$ fields this holds whenever $\langle u, \mathbf{J}_x F^{(i)} u\rangle \le -\rho(i)\|u\|^2$ for all $u, x$; for gradient fields $F^{(i)} = -\nabla V_i$ it is $\rho(i)$-strong convexity of $V_i$.)

**Theorem.** If

$$\sum_{i \in F} \rho(i)\,\nu(i) > 0,$$

then $(X_t, I_t)$ converges in law to a unique invariant probability measure, whatever the initial condition.

**Counterpoint (switching can destabilise).** Stability of every field separately is not enough. In $\mathbb{R}^2$ with $F = \{0,1\}$, symmetric switching rate $\lambda$, and the linear Hurwitz fields

$$F^{(0)}(v) = \begin{pmatrix} -1 & 4 \\ -1/4 & -1\end{pmatrix} v, \qquad F^{(1)}(v) = \begin{pmatrix} -1 & -1/4 \\ 4 & -1\end{pmatrix} v,$$

there is a critical rate $\beta_c > 0$ such that $\|X_t\| \to 0$ exponentially fast if $\lambda < \beta_c$ and $\|X_t\| \to \infty$ exponentially fast if $\lambda > \beta_c$.

## Proof sketch

Two copies of the process driven by the same environment path satisfy $\frac{d}{dt}\|X_t - Y_t\|^2 \le -2\rho(I_t)\|X_t - Y_t\|^2$, so $\|X_t - Y_t\|^2 \le \exp(-2\int_0^t \rho(I_s)\,ds)\|X_0 - Y_0\|^2$, and the ergodic theorem for $I$ turns the exponent into $-2t\sum_i \rho(i)\nu(i) + o(t)$: contraction on average forces synchronous coupling and hence uniqueness. Existence of the invariant law uses a Lyapunov function and a Harris-type theorem adapted to PDMPs. The counterexample shows why only the averaged contraction rate, not individual stability, controls the switched system.

## Sources

- Bertrand Cloez, Renaud Dessalles, Alexandre Genadot, Florent Malrieu, Aline Marguet and Romain Yvinec, "Probabilistic and Piecewise Deterministic models in Biology", *ESAIM: Proceedings and Surveys* 60 (2017), 225–245, <https://doi.org/10.1051/proc/201760225>. Preprint version: arXiv:1706.09163 (2017), Section 2 (Theorem 2, Lemma 3 and Theorem 4), <https://doi.org/10.48550/arXiv.1706.09163>.
