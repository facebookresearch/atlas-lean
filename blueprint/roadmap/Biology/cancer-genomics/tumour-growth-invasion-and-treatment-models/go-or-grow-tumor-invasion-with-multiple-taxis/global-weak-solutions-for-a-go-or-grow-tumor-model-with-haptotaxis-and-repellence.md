# Global weak solutions for a go-or-grow tumor model with haptotaxis and interspecies repellence

**Model.** Tumor cells come in two mutually exclusive phenotypes: migrating cells $m$ and proliferating cells $p$, invading tissue (extracellular matrix) of density $v$. Migrating cells diffuse nonlinearly, climb tissue gradients (haptotaxis) and move away from proliferating cells (unilateral repellence); proliferating cells and tissue do not move. A simplified version of the multiscale model, on a bounded smooth domain $\Omega\subset\mathbb{R}^n$, $n\le3$, is

$$\begin{aligned}\partial_tm&=\nabla\cdot\big(D(m,p,v)\nabla m\big)-\nabla\cdot\Big(\frac{c_1v}{1+v}\,m\nabla v\Big)+\nabla\cdot(c_2\,m\nabla p)+\lambda p-\gamma m,\\ \partial_tp&=\mu p\big(1-(m+p)-\eta_1v\big)-\lambda p+\gamma m,\\ \partial_tv&=-\alpha mv-\beta pv+\mu_v v(1-v),\end{aligned}$$

with no-flux boundary conditions, phenotype switching rates $\lambda$ ($p\to m$) and $\gamma$ ($m\to p$), and all parameters positive. Initial data: $m_0\in C^0(\bar\Omega)$, $p_0,v_0\in W^{1,2}\cap C^0(\bar\Omega)$, all nonnegative. The diffusivity satisfies (3.5): $D\in C^3([0,\infty)^3)\cap W^{2,\infty}\big([0,\infty)\times[0,A]\times[0,L]\big)$ and $0<C_2\le D(m,p,v)\le C_1$ there, where $A=\max\{\|p_0\|_\infty,1-\lambda/\mu,\gamma/\mu\}$ and $L=\max\{\|v_0\|_\infty,1\}$ bound $p$ and $v$.

**Theorem.** If the repellence sensitivity is small, $0<c_2<\dfrac{4\gamma C_2}{\mu A^2}$, there is a global weak solution, which moreover satisfies

$$m\in L^\infty\big((0,\infty);L^1(\Omega)\big),\qquad p,v\in L^\infty\big(\Omega\times(0,\infty)\big),$$

where, for the approximating solutions, $\int_\Omega m(\cdot,t)\le\max\{\int_\Omega m_0,\ \lambda A|\Omega|/\gamma\}$.

## Expansion

The ODEs for $p$ and $v$ give the pointwise bounds $p\le A$, $v\le L$ by comparison, and integrating the $m$ equation gives the $L^1$ bound because switching to the proliferating state removes mass at rate $\gamma m$ while supply is at most $\lambda A$. Since $p$ and $v$ do not diffuse, their gradients must be controlled through their own equations. The key estimate is an energy functional

$$\int_\Omega m\ln m+\int_\Omega\frac{|\nabla v|^2}{1+v}+\int_\Omega|\nabla p|^2,$$

whose dissipation controls $D|\nabla m|^2/m$, $m|\nabla v|^2/(1+v)^2$ and $m|\nabla p|^2$ uniformly for a regularized problem. The smallness condition $c_2<4\gamma C_2/(\mu A^2)$ is what lets the repellence cross term be absorbed in this estimate; compactness then passes to the limit in the regularization. Simulations of the full model compare it with a variant in which repellence is mediated by a diffusing chemorepellent.

## Sources

- Niklas Kolbe, Nikolaos Sfakianakis, Christian Stinner, Christina Surulescu and Jonas Lenz, "Modeling multiple taxis: tumor invasion with phenotypic heterogeneity, haptotaxis, and unilateral interspecies repellence", arXiv:2005.01444 (2020), Section 3, system (3.1)–(3.3), assumption (3.5), Lemma 3.4, Proposition 3.6 and Theorem 3.2, <https://doi.org/10.48550/arXiv.2005.01444>.
