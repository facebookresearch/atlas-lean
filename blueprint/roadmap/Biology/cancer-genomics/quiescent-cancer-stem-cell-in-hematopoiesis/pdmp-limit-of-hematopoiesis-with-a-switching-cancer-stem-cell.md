# PDMP limit of hematopoiesis with a single quiescence-switching cancer stem cell

**Microscopic model.** A pool of $K$ healthy hematopoietic stem cells (HSCs) contains $N_1^K(t)$ active cells; $N_2^K$ and $N_3^K$ count healthy and mutant red blood cells; $I^K(t)\in\{0,1\}$ records whether the unique cancer HSC is quiescent ($0$) or active ($1$). The Markov jump dynamics are: quiescent healthy HSCs activate at rate $a$ each ($N_1\to N_1+1$ at rate $a(K-N_1)$); active ones become quiescent at rate $q^K N_1$; healthy red cells are produced at rate $K^{\alpha} r^K N_1$ and die at rate $d$ each; mutant red cells are produced at rate $K^{\beta} r_M^K I$ and die at rate $d_M$ each; the cancer HSC activates at rate $a_M$ and becomes quiescent at rate $q_M^K$. The regulation functions are evaluated at the rescaled red-cell counts, $q^K(n_2,n_3) = q(n_2/K^{1+\alpha}, n_3/K^{\beta})$ and similarly for $q_M^K,r^K,r_M^K$, where
$q(x_2,x_3) = q_1+q_2x_2+q_3x_3$, $q_M(x_2,x_3) = q_{1,M}+q_{2,M}x_2+q_{3,M}x_3$, $r(x_2,x_3) = c_1/(1+c_2x_2+c_3x_3)$, $r_M(x_2,x_3) = c_{1,M}/(1+c_{2,M}x_2+c_{3,M}x_3)$, with $a,q_1,q_{1,M},c_1,c_{1,M},d,d_M>0$ and the remaining coefficients $\ge 0$; $\alpha,\beta>0$ encode the amplification from stem cells to red cells.

**Scaling.** Set $X^K = \big(N_1^K/K,\; N_2^K/K^{1+\alpha},\; N_3^K/K^{\beta}\big)$. If $\sup_K\mathbb{E}\|X^K(0)\|^2<\infty$, then $\sup_K\mathbb{E}\sup_{t\le T}\|X^K(t)\|^2<\infty$ for every $T$.

**Theorem (convergence to a PDMP).** If $(X^K(0),I^K(0))$ converges in law to $(x_0,i_0)$ with uniformly bounded second moments, then $(X^K,I^K)$ converges in law in the Skorokhod space $\mathbb{D}([0,T],\mathbb{R}_+^3\times\{0,1\})$ to the piecewise deterministic Markov process $(X,I)$ with generator

$$
\mathcal{L}f(x,i) = \sum_{j=1}^3 g_j(x,i)\,\partial_{x_j} f(x,i) + a_M(1-i)\big(f(x,1)-f(x,0)\big) + q_M(x_2,x_3)\,i\,\big(f(x,0)-f(x,1)\big),
$$

$$
g(x,i) = \big(a-(a+q(x_2,x_3))x_1,\; r(x_2,x_3)x_1 - d x_2,\; r_M(x_2,x_3)\,i - d_M x_3\big)^{\mathsf T}.
$$

Between switches of the cancer-cell state $I$, the macroscopic populations $X$ follow the ODE $\dot X = g(X,I)$; the single cancer stem cell keeps its stochastic on/off dynamics in the limit, with switching rates that depend on $X$.

## Expansion

Write $(X^K,I^K)$ as semimartingales. The martingale parts of $X^K$ have predictable quadratic variations of order $K^{-1}$, $K^{-(1+\alpha)}$ and $K^{-\beta}$, so they vanish uniformly in probability by Doob's inequality, while $I^K$ is not rescaled and keeps an order-one jump martingale. The Aldous–Rebolledo criteria give tightness; jumps of $X^K$ are at most of order $K^{-(1\wedge\beta)}$, so limits have continuous $X$. A Taylor expansion shows $\mathcal{L}^K f\to\mathcal{L}f$ uniformly for $f\in C^1_b$, identifying any limit as a solution of the coupled Cauchy/martingale problem, which is pathwise unique by Cauchy–Lipschitz once $I$ is represented through a Poisson point measure.

## Sources

- C. Bonnet, "A PDMP to model the stochastic influence of quiescence dynamics in blood cancers", arXiv:2303.06412 (2023), Section 2 (model, Lemma 1 and Theorem 1), <https://doi.org/10.48550/arXiv.2303.06412>.
