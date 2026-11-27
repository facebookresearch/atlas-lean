# Switching between Lotka–Volterra systems with a common equilibrium prevents convergence

For $i \in E = \{0,1\}$ let

$$F^i(x,y) = \begin{pmatrix} x(a_i - b_i y)\\ y(-c_i + d_i x)\end{pmatrix}, \qquad a_i,b_i,c_i,d_i > 0,$$

be Lotka–Volterra predator-prey vector fields (prey $x$, predator $y$), with positive equilibria $(c_i/d_i, a_i/b_i)$. Let $(I_t)$ be a continuous-time Markov chain on $E$ with jump rates $k_0, k_1 > 0$, and let $X_t = (x_t, y_t)$ solve $\dot X_t = F^{I_t}(X_t)$ from $X_0 \in \mathbb{R}^2_{++}$; $(X,I)$ is a piecewise deterministic Markov process. Assume the two systems have a **common** equilibrium $(p,q) = (c_0/d_0, a_0/b_0) = (c_1/d_1, a_1/b_1)$ and that $F^0, F^1$ are not collinear.

**Theorem.** There exist $\varepsilon > 0$, $\eta > 1$, $\theta > 0$ and $C > 0$ such that for all $\mathbf{x} \in \mathbb{R}^2_{++} \setminus \{(p,q)\}$ and $i \in E$,

$$\mathbb{E}_{\mathbf{x},i}\big[\eta^{\tau^\varepsilon}\big] \le C\big(1 + \|\mathbf{x} - (p,q)\|^{-\theta}\big), \qquad \tau^\varepsilon = \inf\{t \ge 0 : \|X_t - (p,q)\| \ge \varepsilon\}.$$

Consequently, for every initial condition $(x_0,y_0) \ne (p,q)$, almost surely

$$\limsup_{t\to\infty}x_t = \limsup_{t\to\infty}y_t = +\infty, \qquad \liminf_{t\to\infty}x_t = \liminf_{t\to\infty}y_t = 0 .$$

Each deterministic system has only neutrally stable closed orbits around $(p,q)$, and an earlier dichotomy showed that the switched process either converges to $(p,q)$ almost surely or oscillates as above; the theorem shows convergence never happens.

## Expansion

Near the common equilibrium the process is governed by the linear switched system $\dot u = A_{I_t}u$ with $A_i = DF^i(p,q)$, matrices with purely imaginary eigenvalues. The key step shows that this linear random product has a strictly positive top Lyapunov exponent: switching between two distinct centers produces net radial growth, proved through an invariant measure of the projected angular process and a multiplicative-system framework. A positive exponent yields a Lyapunov function $V \approx \|u\|^{-\theta}$ that decreases geometrically in expectation near $(p,q)$, giving the exponential moment bound for the exit time $\tau^\varepsilon$. Hence the process leaves every neighbourhood of the equilibrium, which excludes the convergence alternative of the dichotomy.

## Sources

- Alexandru Hening, Edouard Strickler, "On a Predator-Prey System with Random Switching that Never Converges to its Equilibrium", SIAM Journal on Mathematical Analysis 51 (2019), 3625–3640, <https://doi.org/10.1137/18m1196042>. Published version of arXiv:1710.01220, cited next; locators there refer to the arXiv version.
- Alexandru Hening, Edouard Strickler, "On a predator-prey system with random switching that never converges to its equilibrium", arXiv (2017). Section 1 (model, dichotomy theorem, main theorem), Section 2 (Definitions 2.1, 2.3, linear switched systems), Section 3. <https://doi.org/10.48550/arXiv.1710.01220>
