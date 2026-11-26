# Discrete Pontryagin conditions for regional vaccination in a multi-region SIR model

**Model.** Regions $\Omega_1, \dots, \Omega_p$ have populations $N^j = S_i^j + I_i^j + R_i^j$ at time steps $i = 0, 1, \dots, N$. Infection in $\Omega_j$ is driven by infectives of every region, with coefficients $\beta_{jk} \ge 0$, under standard incidence; $d_j$ is the common birth and death rate and $\gamma_j$ the recovery rate. A vaccination control $u_i^j \in [u_{\min}^j, u_{\max}^j] \subset (0, 1)$ moves susceptibles to the removed class:

$$\begin{aligned}
S_{i+1}^j &= S_i^j - \sum_{k=1}^{p} \beta_{jk} \frac{I_i^k}{N^j} S_i^j + d_j (N^j - S_i^j) - u_i^j S_i^j,\\
I_{i+1}^j &= I_i^j + \sum_{k=1}^{p} \beta_{jk} \frac{I_i^k}{N^j} S_i^j - (\gamma_j + d_j) I_i^j,\\
R_{i+1}^j &= R_i^j + \gamma_j I_i^j - d_j R_i^j + u_i^j S_i^j .
\end{aligned}$$

Summing the three equations shows that $N^j$ is constant in time.

**Control problem.** For weights $\alpha_j^I, \alpha_j^R, A_j > 0$, minimize

$$J_j(u^j) = \alpha_j^I I_N^j - \alpha_j^R R_N^j + \sum_{i} \Bigl( \alpha_j^I I_i^j - \alpha_j^R R_i^j + \frac{A_j}{2} (u_i^j)^2 \Bigr)$$

over admissible sequences $u^j = (u_0^j, \dots, u_{N-1}^j)$. Because the state space is finite-dimensional and the control set compact, an optimal control exists.

**Necessary conditions.** With the Hamiltonian

$$H_i^j = \alpha_j^I I_i^j - \alpha_j^R R_i^j + \frac{A_j}{2} (u_i^j)^2 + \zeta_{1,i+1}^j S_{i+1}^j + \zeta_{2,i+1}^j I_{i+1}^j + \zeta_{3,i+1}^j R_{i+1}^j ,$$

where $S_{i+1}^j, I_{i+1}^j, R_{i+1}^j$ stand for the right-hand sides of the model, an optimal $(u^{j\ast}, S^{j\ast}, I^{j\ast}, R^{j\ast})$ admits costates satisfying the backward recursions

$$\zeta_{1,i}^j = \frac{\partial H_i^j}{\partial S_i^j}, \qquad \zeta_{2,i}^j = \frac{\partial H_i^j}{\partial I_i^j}, \qquad \zeta_{3,i}^j = \frac{\partial H_i^j}{\partial R_i^j},$$

with transversality conditions $\zeta_{1,N}^j = 0$, $\zeta_{2,N}^j = \alpha_j^I$, $\zeta_{3,N}^j = -\alpha_j^R$, and the optimal control is

$$u_i^{j\ast} = \min\Bigl\{ \max\Bigl\{ u_{\min}^j,\ \frac{(\zeta_{1,i+1}^j - \zeta_{3,i+1}^j)\, S_i^{j\ast}}{A_j} \Bigr\},\ u_{\max}^j \Bigr\}, \qquad i = 0, \dots, N - 1 .$$

## Expansion

The Hamiltonian is strictly convex in $u_i^j$ with $\partial H_i^j / \partial u_i^j = A_j u_i^j - (\zeta_{1,i+1}^j - \zeta_{3,i+1}^j) S_i^j$, so the unconstrained minimizer is $(\zeta_{1,i+1}^j - \zeta_{3,i+1}^j) S_i^j / A_j$ and projecting onto the admissible interval gives the formula. The costate difference $\zeta_1 - \zeta_3$ is the marginal value of moving one person from susceptible to removed at the next step, so vaccination is intense when many susceptibles remain and the shadow cost of a susceptible is high. The terminal costates are the gradients of the terminal cost $\alpha_j^I I_N - \alpha_j^R R_N$. The optimality system (forward states, backward costates, projected control) is solved by forward–backward sweeps; the same construction extends to a travel-blocking control that reduces the cross-regional coefficients $\beta_{jk}$, $k \ne j$.

## Sources

- O. Zakary, M. Rachik, I. Elmouki, "On the analysis of a multi-regions discrete SIR epidemic model: an optimal control approach", International Journal of Dynamics and Control 5 (2017) 917–930, Equations (1)–(12), Theorems 3.2.1 and 3.2.2, <https://doi.org/10.1007/s40435-016-0233-2> (PMC7133609).
