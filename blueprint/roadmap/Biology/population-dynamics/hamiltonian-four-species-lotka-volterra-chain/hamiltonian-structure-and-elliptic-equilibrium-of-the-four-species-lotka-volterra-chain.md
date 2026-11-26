# Hamiltonian structure and elliptic equilibrium of the four-species Lotka–Volterra chain

**Model.** Four species with a strict trophic hierarchy ($x_1$ apex predator, $x_4$ prey of all, $x_2,x_3$ intermediate) evolve by

$$
\dot{\mathbf x}=\mathbf x\odot(A\mathbf x+\mathbf r),\qquad
A=\begin{pmatrix}0&a_2&a_3&a_4\\-a_1&0&a_3&a_4\\-a_1&-a_2&0&a_4\\-a_1&-a_2&-a_3&0\end{pmatrix},\quad a_i>0,
$$

where $\odot$ is the entrywise product, so each extinction hyperplane $x_i=0$ is invariant. After rescaling, $a_i=1$ without loss of generality:

$$
\dot x_1=x_1(x_2+x_3+x_4+r_1),\ \ \dot x_2=x_2(-x_1+x_3+x_4+r_2),\ \ \dot x_3=x_3(-x_1-x_2+x_4+r_3),\ \ \dot x_4=x_4(-x_1-x_2-x_3+r_4).
$$

**Hamiltonian structure.** On the positive orthant the system is Hamiltonian for the log-canonical Poisson bracket $\{x_i,x_j\}=x_ix_j$ ($i<j$) with

$$
H(\mathbf x)=\sum_{i=1}^4\big(x_i+k_i\log x_i\big),\qquad
k_1=-r_2+r_3-r_4,\ k_2=r_1-r_3+r_4,\ k_3=-r_1+r_2-r_4,\ k_4=r_1-r_2+r_3 .
$$

**Proposition (elliptic equilibrium).** The system has a single elliptic equilibrium, located at

$$
\mathbf x_0=-\mathbf k=(r_2-r_3+r_4,\ -r_1+r_3-r_4,\ r_1-r_2+r_4,\ -r_1+r_2-r_3),
$$

if and only if

$$
\sum_{i<j}k_ik_j>0\qquad\text{and}\qquad\prod_{i=1}^4k_i>0 .
$$

**Lemma (first integrals).** Let

$$
I_1=\frac{x_2+x_3}{x_1x_4},\qquad I_2=\frac{(x_3+x_4)x_1}{x_2},\qquad I_3=\frac{(x_1+x_2)x_4}{x_3},
$$

the three independent first integrals of the case $\mathbf r=0$ (where $H_0=x_1+x_2+x_3+x_4=(I_1-1)I_2I_3$). If a differentiable $\Phi$ on a domain of $\mathbb R^3$ satisfies

$$
\frac{k_3x_2-k_2x_3}{x_2+x_3}\,I_1\partial_{I_1}\Phi+\frac{k_4x_3-k_3x_4}{x_3+x_4}\,I_2\partial_{I_2}\Phi+\frac{k_2x_1-k_1x_2}{x_1+x_2}\,I_3\partial_{I_3}\Phi=0,
$$

then $\Phi(I_1,I_2,I_3)$ is a first integral. This recovers the two-parameter integrable families, e.g. $\mathbf k=(k_1,0,0,k_4)$ with integral $I_1$, $\mathbf k=(k_1,k_2,0,0)$ with $I_2$, $\mathbf k=(0,0,k_3,k_4)$ with $I_3$, and $\mathbf k=(k_1,-k_1,k_3,-k_3)$ with $I_2^{k_1}I_3^{-k_3}$.

## Expansion

The equilibrium is $\mathbf x_0=-A^{-1}\mathbf r=-\mathbf k$, and it lies in the open positive orthant exactly when all $k_i<0$. The Jacobian there has rows $(0,-k_1,-k_1,-k_1)$, $(k_2,0,-k_2,-k_2)$, $(k_3,k_3,0,-k_3)$, $(k_4,k_4,k_4,0)$; its characteristic polynomial is even, $\lambda^4+\alpha\lambda^2+\beta$ with $\alpha=\sum_{i<j}k_ik_j$ and $\beta=\prod_ik_i$, so the eigenvalues are $\pm i\sqrt{(\alpha\pm\sqrt{\alpha^2-4\beta})/2}$ and the sign conditions on $\alpha,\beta$ make them purely imaginary. The other seven equilibria (origin and six on coordinate planes) always have real eigenvalues. The dichotomy that follows is biological: on integrable parameter sets the extra invariants confine trajectories so that populations grow without bound or collapse (no sustainable coexistence), whereas non-integrable parameter sets near an elliptic $\mathbf x_0$ show bounded chaotic motion (positive Lyapunov exponents, structured Poincaré sections) in which all four species persist.

## Sources

- H. Christodoulidi, T. E. Kouloukas, L. B. Drossos, T. Bountis, "Integrable and Chaotic 4-Dimensional Lotka–Volterra Models and Population Sustainability", arXiv:2609.13797 (2026), Section 2 (model, Poisson structure, Hamiltonian), Section 3 Proposition 1, Section 4 Lemma 1, <https://doi.org/10.48550/arXiv.2609.13797>.
