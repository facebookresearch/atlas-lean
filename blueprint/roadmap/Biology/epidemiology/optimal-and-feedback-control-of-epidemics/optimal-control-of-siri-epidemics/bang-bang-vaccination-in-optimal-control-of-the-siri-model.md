# Optimal protection and vaccination in the SIRI model with reinfection

**Controlled SIRI model.** Population fractions $x_S,x_I,x_R\in[0,1]$ with $x_S+x_I+x_R=1$ evolve under a protection input $u_P(t)\in[u_{P\min},1]$ (the factor by which contacts are scaled; $u_P=1$ means no protection) and a vaccination input $u_V(t)\in[0,u_{V\max}]$:

$$\dot x_S=-\beta x_Sx_Iu_P-x_Su_V,\qquad \dot x_I=\beta x_Sx_Iu_P+\hat\beta x_Rx_Iu_P-\gamma x_I,\qquad \dot x_R=-\hat\beta x_Rx_Iu_P+x_Su_V+\gamma x_I .$$

Recovered (or vaccinated) individuals can be reinfected at rate $\hat\beta$; $\hat\beta=0$ gives SIR and $\hat\beta=\beta$ gives SIS. The simplex $\{x \ge 0,\ x_S+x_I+x_R=1\}$ is positively invariant. (The source's Lemma 2.1 states invariance of the cube $[0,1]^3$, which fails: from $(0,1,1)$, $\dot x_I=\hat\beta u_P-\gamma>0$ when $\hat\beta u_P>\gamma$.)

**Equilibria.** For constant inputs with $u_V^{\rm eq}>0$, the disease-free point $(0,0,1)$ always exists and the endemic point $\bigl(0,\,1-\tfrac{\gamma}{\hat\beta u_P^{\rm eq}},\,\tfrac{\gamma}{\hat\beta u_P^{\rm eq}}\bigr)$ exists iff $\gamma<\hat\beta u_P^{\rm eq}$. The disease-free point is locally asymptotically stable iff $\gamma>\hat\beta u_P^{\rm eq}$ and the endemic point iff $\gamma<\hat\beta u_P^{\rm eq}$: once vaccination empties the susceptible class, persistence is decided by the *reinfection* reproduction number $\hat\beta u_P^{\rm eq}/\gamma$.

**Optimal control problem.** Minimize over $[0,T]$ the cost of protection, infection and vaccination, proportional to the mass adopting each,

$$J=\int_0^T\Bigl[c_P\,(x_S+x_R)(1-u_P)+c_I\,x_I+c_V\,x_Su_V\Bigr]dt ,$$

subject to the dynamics and input bounds.

**Theorem.**

1. An optimal control exists (Filippov's theorem: the dynamics and running cost are affine in the inputs over a compact convex input set).
2. If reinfection is more transmissible than first infection, $\hat\beta>\beta$, the candidate optimal inputs $u_P^*$ and $u_V^*$ cannot both be singular on any open time interval.
3. If moreover $(\beta-\hat\beta)(c_I-c_P)\ne-\beta c_V\gamma$, $(\beta-\hat\beta)c_I+\beta\hat\beta c_V-\beta c_V\gamma<0$ and $(\beta-\hat\beta)\bigl(c_I-c_P(1-u_{P\min})\bigr)+\beta\hat\beta c_Vu_{P\min}<0$, then $u_V^*$ is never singular: the optimal vaccination policy is bang-bang, switching between $0$ and $u_{V\max}$.

## Expansion

In Mayer form with an extra cost state, the system is control-affine, $\dot{\mathbf z}=\mathbf f(\mathbf z)+\mathbf g_P(\mathbf z)u_P+\mathbf g_V(\mathbf z)u_V$, so Pontryagin's principle makes each input bang-bang wherever its switching function $\lambda\cdot\mathbf g_P$ or $\lambda\cdot\mathbf g_V$ is nonzero. On a singular arc the switching function and its time derivatives vanish; these derivatives are Lie brackets of $\mathbf f,\mathbf g_P,\mathbf g_V$ paired with the costate. Under $\hat\beta>\beta$ the brackets for a doubly singular arc are linearly independent, forcing a zero costate, which contradicts the maximum principle; the parameter inequalities do the same for a vaccination-only singular arc, leaving protection as the only input that may take intermediate values.

## Sources

- Urmee Maitra, Ashish R. Hota, Rohit Gupta, Alfred O. Hero, "Optimal protection and vaccination against epidemics with reinfection risk", AIMS Mathematics 10 (2025), 10140–10162, <https://doi.org/10.3934/math.2025462>. Published version of arXiv:2504.08191, cited next; locators there refer to the arXiv version.
- U. Maitra, A. R. Hota, R. Gupta, A. O. Hero, "Optimal protection and vaccination against epidemics with reinfection risk", arXiv:2504.08191 (2025), Section 2 (controlled SIRI model, Lemma 2.1, equilibria and their local stability proposition), Section 3 (optimal control problem, Theorem 3.2) and Section 4 (Assumptions 4.1–4.2, the non-simultaneous-singularity proposition and Theorem 4.3). <https://doi.org/10.48550/arXiv.2504.08191>
