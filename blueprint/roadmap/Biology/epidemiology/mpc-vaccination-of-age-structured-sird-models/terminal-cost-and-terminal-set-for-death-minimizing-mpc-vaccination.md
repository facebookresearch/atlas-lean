# Terminal cost and terminal set for death-minimizing MPC vaccination

**Model.** Consider the forward-Euler discretisation (time step one day) of an age-structured SIRD model with $n_a$ age groups and vaccination input $u_k(n)\ge 0$:

$$
\begin{aligned}
S_k(n+1) &= S_k(n) - \lambda_k S_k(n)\sum_{j=1}^{n_a} C_{kj} I_j(n) - u_k(n), \\
I_k(n+1) &= I_k(n) + \lambda_k S_k(n)\sum_{j=1}^{n_a} C_{kj} I_j(n) - (\gamma_{R_k} + \gamma_{D_k}) I_k(n), \\
R_k(n+1) &= R_k(n) + \gamma_{R_k} I_k(n) + u_k(n), \\
D_k(n+1) &= D_k(n) + \gamma_{D_k} I_k(n),
\end{aligned}
$$

where $\lambda_k>0$ is the transmission probability per contact, $C_{kj}\ge 0$ the contact matrix, and $\gamma_{R_k},\gamma_{D_k}>0$ the recovery and death rates. The age-group populations $P\in\mathbb R^{n_a}$ are constant. The state $x = (S,I,R,D)$ lies in $\mathbb X = \{0\le S,I,R,D\le P\}$, the input lies in $\mathbb U = \{u\ge 0,\ \sum_k u_k\le\bar v\}$ (daily vaccine capacity $\bar v$), $\mathbb Z = \mathbb X\times\mathbb U$, and the target set is the infection-free set $X^* = \{x\in\mathbb X: I = 0\}$.

**MPC problem.** At each day solve the $N$-step problem: minimise $\sum_{n=0}^{N-1} l(x(n),u(n)) + V_f(x(N))$ subject to the dynamics, $(x(n),u(n))\in\mathbb Z$ and $x(N)\in\mathbb X_f$. Apply the first input $\kappa_N(x)$. Choose $\epsilon$ with $0<\epsilon<\min_k(\gamma_{R_k}+\gamma_{D_k})$ and set

$$
l(x,u) = \gamma_D^{T} I, \qquad V_f(x) = \frac{1}{\epsilon}\,\gamma_D^{T} I, \qquad
\mathbb X_f = \{x\in\mathbb X : C^{T}\Lambda S \le \Gamma\} \cup X^*,
$$

with $\Lambda = \operatorname{diag}(\gamma_{D_k}\lambda_k)$ and $\Gamma_k = \gamma_{D_k}(\gamma_{R_k} + \gamma_{D_k} - \epsilon)$, the inequality taken componentwise.

**Theorem.** With these choices:

1. for every initial state in the feasibility region $\mathcal X_N$ the MPC problem has a solution (recursive feasibility);
2. the infection-free set $X^*$ is asymptotically stable in $\mathcal X_N$ for the closed loop $x(n+1) = f(x(n),\kappa_N(x(n)))$;
3. the optimal value $V_N^0(x)$ upper-bounds the total number of future deaths under the MPC policy, $\sum_{n\ge 0}\gamma_D^{T} I(n)$.

## Expansion

The proof checks the standard sufficient conditions for MPC stability with a terminal ingredient (continuity, compact constraint sets, a terminal set that is control invariant with a local Lyapunov terminal cost, and $\mathcal K_\infty$ bounds). The key condition is a one-step decrease of weighted prevalence, $\gamma_D^T I(n+1)\le(1-\epsilon)\gamma_D^T I(n)$. Expanding the dynamics, this holds for every input whenever $\sum_k\gamma_{D_k}\lambda_k S_k C_{kj}\le\Gamma_j$ for all $j$, i.e. $C^T\Lambda S\le\Gamma$. Because $S$ never increases, this set is forward invariant regardless of vaccination. On it, $V_f(f(x,0)) - V_f(x)\le -\gamma_D^T I = -l(x,0)$. The stage cost satisfies $l\ge\min_k\gamma_{D_k}\,\lVert I\rVert_1$, which is the distance to $X^*$, giving the lower $\mathcal K_\infty$ bound. Item 3 follows because the MPC value bounds the infinite-horizon cost along the closed loop, and summed daily deaths telescope to the final death toll. Epidemiologically, $\mathbb X_f$ is the region of susceptible depletion in which the death-weighted effective reproduction is below $1-\epsilon$.

## Sources

- Candy Sonveaux, Morgane Dumont, Mirko Fiacchini, Mohamad Ajami, "An Age-Structured Vaccination Strategy for Epidemic Containment: A Model Predictive Control Approach", arXiv 2026: Section 2 (age-structured SIRD model), Section 3, Theorem 1 (recalled standard MPC stability result), Corollary 1, Theorem 2. <https://doi.org/10.48550/arXiv.2602.14758>
