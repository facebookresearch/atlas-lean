# Equilibria of finite-state graphon games for epidemic control

**Model.** A continuum of players indexed by $x\in I=[0,1]$ moves on a finite state space $E$ (for example $E=\{S,I,R\}$). Heterogeneous interactions are given by a graphon $w:I\times I\to[0,1]$. Player $x$ in state $e$ chooses a control $a$ (for instance a contact factor) and jumps to $e'$ at rate $q^x_{e,e'}(a,Z^x_t)$, where the *neighbourhood aggregate* is

$$Z^x_t=\int_Iw(x,y)\sum_{e\in E}K\big(\phi^y(t,e),e\big)\,p^y(t,e)\,dy,$$

$p^y(t,\cdot)$ is the state distribution of player $y$, and $K$ weights states and controls (e.g. infectious players' contact levels). Each player minimizes an expected running cost $f^x$ plus terminal cost $g^x(e,Z^x_T)$ given the aggregate flow. A Nash equilibrium is a family of controls $\hat\phi^x$ optimal for every $x$ against the aggregate they jointly generate.

**Theorem (verification).** If $u^x(t,e)$ is a $C^1$ solution of the HJB system $\dot u^x(t,e)=-\hat H^x\big(t,e,Z^x_t,\Delta_eu^x(t,\cdot)\big)$, $u^x(T,e)=g^x(e,Z^x_T)$, with $\Delta_eu(e')=u(e')-u(e)$ and $\hat H$ the minimized Hamiltonian, then $u^x$ is the value function for the given flow, and the Hamiltonian minimizer $\hat\phi^x(t,e)=\hat a^x_e(t,Z^x_t,u^x(t,\cdot))$ is an optimal Markov control.

**Theorem (existence of equilibrium).** Assume, with $A$ the control set:

- (rates, Condition 2.3) $|q^x_{e,e'}(a,z)|\le q_{\max}$ for all $x,e,e',a,z$, and there is $C$ with $|q^x_{i,k+i}(a,z)-q^x_{j,k+j}(a,z')|\le C\big(\mathbf 1_{\{i\ne j\}}+|z-z'|^p\big)$ for $p=1,2$ (indices of $E$ taken cyclically);
- (impact, Condition 2.4) $|K(a,e)-K(a',e)|\le L_K|a-a'|$ and $|K(a,e)|\le C_K$;
- (control-affine rates and convex costs, Condition 2.7) the rate matrix is $Q^x(a,z)=Q_1(z)+aQ_2(z)$ with $Q_2$ locally Lipschitz; $a\mapsto f^x(t,e,z,a)$ is $C^1$ and strongly convex uniformly in $(t,e,z)$, with $(t,z)\mapsto\partial_af^x$ locally Lipschitz uniformly in $(a,e)$; $f$ and $g$ are uniformly bounded and $z\mapsto f^x(t,e,z,a)$ is continuous.

These make the Hamiltonian minimizer $\hat a$ locally Lipschitz. If

$$\|w\|_{L^2(I\times I)}\,L_K\,L_{\hat a}(C_K)<1,$$

where $L_K$ and $L_{\hat a}(C_K)$ are Lipschitz constants of $K$ and of the minimizer on the relevant bounded set, then the continuum of coupled forward–backward ODEs

$$\begin{aligned} \dot p^x(t,e)&=\sum_{e'}q^x_{e',e}\big(\hat\phi^x(t,e'),Z^x_t\big)p^x(t,e'),&p^x(0,\cdot)&=p^x_0,\\ \dot u^x(t,e)&=-\hat H^x\big(t,e,Z^x_t,\Delta_eu^x(t,\cdot)\big),&u^x(T,\cdot)&=g^x(\cdot,Z^x_T), \end{aligned}$$

closed by the aggregate formula above, has a bounded solution $(u,p)\in C([0,T];L^2(I\times E)^2)$ with each $p^x(t,\cdot)$ a probability vector; the feedback $\hat\phi$ is then a graphon-game equilibrium.

**Theorem (law of large numbers).** On a rich Fubini extension carrying essentially pairwise independent state processes $X^x$, for any admissible control profile the aggregate $Z^x$ is almost surely equal to a deterministic function, continuous in time for every $x$, so the deterministic forward equation for $p^x$ describes the random population exactly.

## Expansion

The forward equation is the Kolmogorov equation of each player's controlled chain; the backward equation is its dynamic-programming equation. Existence is a Banach fixed point on the aggregate: given $Z$, solve the decoupled HJB and Kolmogorov equations, then recompute $Z$; the smallness condition makes this map a contraction in $L^2$ because the graphon enters only through the integral operator with kernel $w$. For an SIR game with contact control the model reproduces heterogeneous lockdown behaviour on structured contact graphs, and a piecewise-constant graphon reduces it to a finite multi-population game.

## Sources

- Alexander Aurell, René Carmona, Gökçe Dayanıklı, Mathieu Laurière, "Finite State Graphon Games with Applications to Epidemics", Dynamic Games and Applications 12 (2022), 49–81, <https://doi.org/10.1007/s13235-021-00410-2>. Published version of arXiv:2106.07859, cited next; locators there refer to the arXiv version.
- Alexander Aurell, René Carmona, Gökçe Dayanıklı, Mathieu Laurière, "Finite State Graphon Games with Applications to Epidemics", arXiv:2106.07859 (2021): Theorem 2.6 (verification), Theorem 2.8 (existence for the forward–backward system), Theorem 4.2 (Fubini extension), Proposition 4.4 and Theorem 4.5 (deterministic aggregate). <https://doi.org/10.48550/arXiv.2106.07859>
