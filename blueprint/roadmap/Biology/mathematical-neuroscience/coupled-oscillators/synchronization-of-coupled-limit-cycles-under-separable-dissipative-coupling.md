# Synchronization of coupled limit cycles under separable dissipative coupling

**Local dynamics.** Let $\dot x=f(x)$, $x\in\mathbb{R}^n$, with $f\in C^2$, have a $1$-periodic orbit $x=u(t)$ with $\dot u\ne0$. Take an orthonormal moving frame $\{v(\theta),z_1(\theta),\dots,z_{n-1}(\theta)\}$ with $v=\dot u/|\dot u|$, and write $Z=(z_1,\dots,z_{n-1})$. Near the orbit, $x=u(\theta)+Z(\theta)\rho$ transforms the system to

$$\dot\theta=1+a(\theta)^{T}\rho+O(|\rho|^2),\qquad \dot\rho=A(\theta)\rho+O(|\rho|^2),\qquad A=Z^TDf(u)Z-Z^TZ'.$$

**Stability assumption.** If $\mu_1(\theta)$ is the largest eigenvalue of the symmetric part $A^s=\tfrac12(A+A^T)$, assume $\int_0^1\mu_1(\theta)\,d\theta=-\mu<0$. This makes $\dot\rho=A(t)\rho$ exponentially stable: $|R(t)R(s)^{-1}|\le C\,e^{-(\mu-\varepsilon)(t-s)}$ for $t\ge s$ and any $0<\varepsilon<\mu$.

**Coupled system.** Couple $N$ copies by $\dot x=f(x)+g\,(\mathbf{D}\otimes L)\,x$, where $x\in\mathbb{R}^{Nn}$, the coupling strength is $g\ge0$, $\mathbf{D}\in\mathbb{R}^{N\times N}$ describes the network, and $L\in\mathbb{R}^{n\times n}$ says which local variables are coupled.

- Assume $\ker\mathbf{D}=\mathrm{span}\{\mathbf{1}_N\}$, so that $\mathbf{1}_N\otimes u(t)$ is a synchronous solution and the network is connected.
- Let $\mathbf{S}\in\mathbb{R}^{(N-1)\times N}$ be the first-difference matrix, and define $\hat{\mathbf{D}}$ by $\mathbf{S}\mathbf{D}=\hat{\mathbf{D}}\mathbf{S}$. Then $\mathbf{D}$ is *dissipative* if $y^T\hat{\mathbf{D}}y<0$ for all $y\ne0$.
- $L$ is symmetric positive semidefinite. The coupling is *full* if $L$ is positive definite and *partial* otherwise.

**Partial-coupling condition.** Let $p_1,\dots,p_l$ be an orthonormal basis of $\ker L$, $O=(v,z_1,\dots,z_{n-1})$, and $c=v^TDf(u)v$. Set

$$L_1^s=\begin{pmatrix}\tfrac12c & v^T(Df)^sZ\\ Z^T(Df)^sv & A^s-\tfrac12c\,I_{n-1}\end{pmatrix},\qquad G_{ij}(t)=\big(L_1^s(t)O^T(t)p_i,\ O^T(t)p_j\big),$$

and let $\lambda_1(t)$ be the largest eigenvalue of $G(t)$. The condition is $\int_0^1\lambda_1(t)\,dt<0$.

**Theorem (synchronization).** Assume the local cycle satisfies the stability assumption, $\mathbf{D}$ is dissipative, and $L$ is positive semidefinite. For partial coupling, also assume the partial-coupling condition. Then for all sufficiently large $g>0$ the coupled system has an exponentially stable synchronous limit cycle.

**Related results.**

- *Consensus.* If $\mathbf{D}$ is dissipative, the linear system $\dot x=\mathbf{D}x$ synchronizes from every initial condition.
- *Characterization.* $\mathbf{D}$ is dissipative iff $\mathbf{D}=\mathbf{Q}\mathbf{S}^T\mathbf{S}$ for some $\mathbf{Q}$ with negative definite symmetric part.
- *Example.* For the radially symmetric oscillator $f(x)=(x_1-x_2-x_1|x|^2,\ x_1+x_2-x_2|x|^2)$, any nonzero positive semidefinite $L$ together with a dissipative $\mathbf{D}$ gives an exponentially stable synchronous cycle. In particular, coupling through a single variable suffices.

## Expansion

Linearize about the synchronous solution and apply $\mathbf{S}\otimes I_n$ to the variational equation. The transverse perturbations then satisfy $\dot\xi=(I\otimes Df(u(t))+g\,\hat{\mathbf{D}}\otimes L)\xi$. In full coupling, $\hat{\mathbf{D}}^s\otimes L$ is negative definite, and large $g$ beats the $O(1)$ Jacobian term. In partial coupling, the coupling term damps only directions outside $I\otimes\ker L$. On $\ker L$ the stability must come from the intrinsic geometry of the limit cycle. Writing the perturbations in the moving frame turns the Jacobian into $L_1^s$, and its averaged quadratic form restricted to $\ker L$ is exactly $\int_0^1\lambda_1<0$. The $\theta$-direction (phase) is neutral within each oscillator but is synchronized through the network term. The analysis applies to compartmental neuron models, where voltage-only (partial) coupling along a linear or branched cable synchronizes the compartments. This approach is complementary to pulse-coupled models of oscillator synchrony.

## Sources

- Georgi S. Medvedev, "Synchronization of Coupled Limit Cycles", Journal of Nonlinear Science 21 (2011), 441–464, <https://doi.org/10.1007/s00332-010-9088-4>; numbering as in arXiv:1005.4074: Lemma 2.1, Assumption 2.2, Lemma 2.3, Definitions 2.4, 2.5 and 2.7, Assumption 2.9, Theorem 2.10, Corollary 3.1, and Theorems 3.3 and 3.4 (Section 3, discussion and examples); proof in Section 4.
