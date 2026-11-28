# Existence of small-tumour equilibrium phases in a size- and space-structured immune model

**Model.** Tumour cells have size density $n(t,z)$ obeying a growth-fragmentation equation with growth rate $V(z)$, division operator $Q$ (mass-conserving, $\int_0^b zQ(n)\,dz=0$) and immune kill $n(t,z)\int_\Omega\delta(y)c(t,y)\,dy$. Antitumour immune cells $c(t,x)$ and protumour immune cells $c_r(t,x)$ move by diffusion and chemotaxis toward a potential $\phi$ solving $-\nabla\cdot(K\nabla\phi)=f(\mu_1)\sigma$, where $\mu_1=\int zn\,dz$ is total tumour mass; tumour-secreted cytokines satisfy $I'=\psi(\mu_1)-\tau I$. Effector cells are activated at rate $g(\mu_1)S$, suppressed by $k_cc\,c_r$ and converted to protumour cells at rate $k_rI\theta c$. Assume $f,g,\psi\ge 0$ nondecreasing, $f(0)=g(0)=\psi(0)=\psi'(0)=0$, $g'(0)S\not\equiv 0$, a kill weight $\delta\ge0$ with $\delta\not\equiv0$, and homogeneous Dirichlet conditions for $c,c_r$. The source's Theorem 1 states no condition on $\delta$, but its proof uses $\partial_{\mu_1}F(0,0)=\int_\Omega\delta C_0'\,dx>0$, which needs $\delta\ge0$, $\delta\not\equiv0$; with $\delta\equiv0$ the constraint $\int_\Omega\delta C\,dx=\ell>0$ cannot hold, so the page states the condition.

**Equilibrium condition.** Let $(\lambda,N)$ be the principal eigenpair of the growth-fragmentation operator, $\partial_z(VN)-Q(N)+\lambda N=0$, $N(0)=0$, $N>0$, $\int N=1$. A tumour equilibrium with size profile proportional to $N$ requires the cytotoxic effector field $C$ to satisfy

$$
\int_\Omega \delta(x)C(x)\,dx=\lambda .
$$

**Statement.** Let $\Phi$ solve $\nabla\cdot(K\nabla\Phi)=\sigma$ with homogeneous Neumann data. There is $\ell^\star>0$ such that for every $0<\ell<\ell^\star$ there exist a unique $\bar\mu_1(\ell)>0$ and a solution $(C,C_r,I)$ of the stationary system

$$
\begin{aligned}
&\gamma C+k_rI\theta C+k_cCC_r-f(\bar\mu_1)\nabla\cdot(C\chi\nabla\Phi)-\nabla\cdot(D\nabla C)=g(\bar\mu_1)S,\\
&\gamma_rC_r-f(\bar\mu_1)\nabla\cdot(C_r\chi\nabla\Phi)-\nabla\cdot(D\nabla C_r)=I(S_r+k_r\theta C),\qquad I=\psi(\bar\mu_1)/\tau,
\end{aligned}
$$

with $C=C_r=0$ on $\partial\Omega$, satisfying $\int_\Omega\delta C\,dx=\ell$; moreover $\ell\mapsto\bar\mu_1(\ell)$ is increasing near $0$. When protumour cells do not alter tumour growth ($b_1=0$), taking $\ell=\lambda<\ell^\star$ yields an equilibrium phase with tumour mass $\bar\mu_1(\lambda)$.

## Expansion

Define $F(\ell,\mu_1)=\int_\Omega\delta C_{\mu_1}\,dx-\ell$. At $\mu_1=0$ all immune fields vanish, so $F(0,0)=0$. Differentiating in $\mu_1$ at $0$, the protumour derivative vanishes because $\psi'(0)=0$, while the effector derivative solves an elliptic problem with nonnegative nontrivial source $g'(0)S$, so the maximum principle gives $C_0'>0$ and $\partial_{\mu_1}F(0,0)>0$. The implicit function theorem then produces the branch $\bar\mu_1(\ell)$, with $\bar\mu_1'(\ell)=1/\partial_{\mu_1}F>0$. The smallness of $\ell$ is the only restriction; for binary division with constant rates $\lambda$ equals the division rate, so the condition is a smallness assumption on that rate. When protumour cells boost growth by a factor $1+\beta_\infty$, the eigenvalue itself depends on $\beta_\infty$ and the argument no longer applies directly.

## Sources

- Atsou K, Anjuère F, Braud VM, Goudon T. A size and space structured model of tumor growth describes a key role for protumor immune cells in breaking equilibrium states in tumorigenesis. *PLoS ONE* (2021) e0259291. <https://doi.org/10.1371/journal.pone.0259291>. PMCID: PMC8608488. Eqs. (12a)-(12g), (21)-(22), (23a)-(23d), Theorem 1.
