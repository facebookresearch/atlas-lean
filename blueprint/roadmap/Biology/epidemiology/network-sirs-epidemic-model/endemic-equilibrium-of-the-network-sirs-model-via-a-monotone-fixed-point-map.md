# Endemic equilibrium of the network SIRS model via a monotone fixed-point map

**Model.** Populations $i\in\mathcal V$ (a finite set) interact through a nonnegative interaction matrix $W\in\mathbb R_+^{\mathcal V\times\mathcal V}$, assumed irreducible (strongly connected interaction graph). With susceptible, infected and recovered fractions $x_i,y_i,z_i$, recovery rates $\gamma_i>0$ and loss-of-immunity rates $\delta_i>0$, the network SIRS model is

$$\dot x_i=-x_i\sum_jW_{ij}y_j+\delta_iz_i,\qquad \dot y_i=x_i\sum_jW_{ij}y_j-\gamma_iy_i,\qquad \dot z_i=\gamma_iy_i-\delta_iz_i ,$$

on $\mathcal X=\{(x,y,z)\ge 0:\ x+y+z=\mathbf 1\}$, which is forward invariant. Write $[\gamma],[\delta]$ for the diagonal matrices of the rates and define

$$R_0=\rho\big([\gamma]^{-1}W\big).$$

**Fixed-point map.** For $\alpha\in\mathbb R_{++}^{\mathcal V}$ let $\Psi(y,\alpha)_i=y_i/(1+(1+\alpha_i)y_i)$, $\mathcal Y_\alpha=\{0\le y_i\le(1+\alpha_i)^{-1}\}$ and $\Phi(y,M,\alpha)=\Psi(My,\alpha)$. Then $(x^\ast,y^\ast,z^\ast)$ is an equilibrium iff

$$y^\ast=\Phi\big(y^\ast,[\gamma]^{-1}W,[\delta]^{-1}\gamma\big),\qquad z^\ast=[\delta]^{-1}[\gamma]y^\ast,\qquad x^\ast=\mathbf 1-y^\ast-z^\ast .$$

**Theorem.** Let $M\ge 0$ be irreducible with dominant eigenvalue $\lambda_M$, $\alpha>0$, and iterate $\xi_{k+1}=\Phi(\xi_k,M,\alpha)$ on $\mathcal Y_\alpha$.
1. If $\lambda_M\le 1$, then $\mathbf 0$ is the only fixed point and $\xi_k\to\mathbf 0$ from every $\xi_0\in\mathcal Y_\alpha$.
2. If $\lambda_M>1$, then there are exactly two fixed points, $\mathbf 0$ and some $y^\ast>\mathbf 0$, and $\xi_k\to y^\ast$ from every $\xi_0>\mathbf 0$.

**Corollary (equilibria of the network SIRS model).** If $R_0\le 1$ the disease-free state $(\mathbf 1,\mathbf 0,\mathbf 0)$ is the unique equilibrium. If $R_0>1$ there is in addition exactly one endemic equilibrium, with $y^\ast>\mathbf 0$ and $z^\ast=[\delta]^{-1}[\gamma]y^\ast$. The endemic prevalence $y^\ast$ is nondecreasing in $[\gamma]^{-1}W$ and nonincreasing in $[\delta]^{-1}\gamma$. Moreover, any positive infection seed spreads to every node instantly: $y(0)\gneq\mathbf 0$ implies $y(t)>\mathbf 0$ for all $t>0$.

## Expansion

$\Phi$ is monotone in $y$ and $M$, antitone in $\alpha$, satisfies $\Phi(\mathbf 0)=\mathbf 0$ and $\Phi(y)<My$ for $y>\mathbf 0$. Iterating from the top element of the box gives a nonincreasing sequence converging to the maximal fixed point $\bar\xi^\ast$. If $\bar\xi^\ast>\mathbf 0$, then $\min_i(M\bar\xi^\ast)_i/\bar\xi^\ast_i>1$, and the Collatz–Wielandt max–min formula forces $\lambda_M>1$; this proves part 1. When $\lambda_M>1$, $\Phi(\varepsilon v)=\lambda_M\varepsilon v+o(\varepsilon)$ along the Perron vector $v$, so iterating from $\varepsilon v$ gives a nondecreasing sequence converging to a positive fixed point. A ratio argument at the node maximizing $\bar\xi^\ast_j/\underline\xi^\ast_j$ shows the smallest and largest positive fixed points coincide, and sandwiching any positive start between them gives convergence. The iteration is also a distributed algorithm for computing the endemic state, though its convergence says nothing about stability of the continuous-time, non-monotone SIRS flow.

## Sources

- Giulia Gatti and Giacomo Como, "On the dynamic behavior of the network SIRS epidemic model", arXiv:2604.21065 (2026), Proposition 1, Lemmas 2–3, Theorem 1 and Corollary 1, <https://doi.org/10.48550/arXiv.2604.21065>.
