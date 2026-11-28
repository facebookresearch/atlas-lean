# Mass concentration on maximal self-renewal clones

Let $\Omega\subset\mathbb R$ be open and bounded. Dividing cells $u_1(t,x)$ and mature cells $u_2(t,x)$ with trait $x$ evolve by

$$\partial_t u_1=\Bigl(\frac{2a(x)}{1+K\rho_2(t)}-1\Bigr)p\,u_1,\qquad \partial_t u_2=2\Bigl(1-\frac{a(x)}{1+K\rho_2(t)}\Bigr)p\,u_1-d\,u_2,\qquad \rho_i(t)=\int_\Omega u_i(t,x)\,dx,$$

where $p,d,K>0$ are the proliferation rate, death rate of mature cells and feedback strength, and $a\in C(\overline\Omega)$, $0<a<1$, is the self-renewal fraction. Assume $u_1^0,u_2^0\in L^1(\Omega)$ are strictly positive a.e., and, in items 1–3, that $\Omega_a=\arg\max_{\overline\Omega}a$, with $\bar a=\max a$, is either a single point or a set of positive measure.

**Theorem.**
1. $u_1,u_2$ converge as $t\to\infty$ to stationary measures supported in $\Omega_a$; outside $\Omega_a$ the solution decays to $0$ exponentially, and $u_1(t,x_1)/u_1(t,x_2)$ is constant in time whenever $a(x_1)=a(x_2)$.
2. If $\bar a>\tfrac12$, the total masses converge to the equilibrium of the ODE model with self-renewal $\bar a$:

$$\bar\rho_1=\frac dp\,\frac{2\bar a-1}{K},\qquad \bar\rho_2=\frac{2\bar a-1}{K}.$$

If $\Omega_a=\{\bar x\}$, then $(u_1,u_2)\to(\bar\rho_1,\bar\rho_2)\,\delta_{\bar x}$ in the bounded Lipschitz (flat) distance; if $|\Omega_a|>0$, convergence is strong in $L^1(\Omega)$ to multiples of $u_i^0\mathbf 1_{\Omega_a}$.
3. If $\bar a\le\tfrac12$, then $u_1,u_2\to 0$ in $L^1(\Omega)$.
4. (Coexistence; here $\Omega_a=\{\bar x_1,\bar x_2\}$.) If $\bar a>\tfrac12$, $u^0_i\in C(\Omega)$ and $u_1^0>0$ on $\Omega_a$: when a $C^1$ diffeomorphism $\Phi$ from a neighbourhood of $\bar x_1$ with $\Phi(\bar x_1)=\bar x_2$ and $a=a\circ\Phi$ exists, the limit is a combination of Dirac masses at both points with strictly positive weights; when $\Phi$ is only a homeomorphism whose inverse has singular Jacobian at $\bar x_2$, all the mass concentrates at $\bar x_2$. Theorem 3 states "strictly positive constants" without $\bar a>1/2$; the limit masses in Corollary 2 are multiples of $2\bar a-1$.

## Expansion

Positivity and boundedness of $\rho_1,\rho_2$ come from the feedback: large $\rho_2$ pushes the growth factor $2a/(1+K\rho_2)-1$ negative. For $x_1,x_2$ the ratio $u_1(t,x_1)/u_1(t,x_2)$ has logarithmic derivative $2p(a(x_1)-a(x_2))/(1+K\rho_2)$, so it decays exponentially when $a(x_1)<a(x_2)$, which gives concentration on $\Omega_a$. Mass convergence follows from a Lyapunov-type argument comparing the dynamics with the ODE system at $\bar a$. In the coexistence case the weights of the two Dirac masses depend on how fast the mass near each maximum is lost, that is on the local shape of $a$: two maxima with Taylor expansions of the same order coexist, while a flatter maximum (e.g. quartic against quadratic) wins.

## Sources

- J.-E. Busse, P. Gwiazda, A. Marciniak-Czochra, "Mass concentration in a nonlocal model of clonal selection", Journal of Mathematical Biology 73(4) (2016) 1001–1033, <https://doi.org/10.1007/s00285-016-0979-3>, PMCID PMC5018043. Eq. (3), Assumption 1, Theorems 1–3, Corollaries 1–2, Lemma 3 and Remark 4.
