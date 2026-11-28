# Optimal lockdown of an SIR epidemic with a controlled stochastic transmission rate

**Model.** Susceptible and infected fractions $(S_t,I_t)$ follow the SIR dynamics with recovery rate $\alpha$ and a random transmission rate $\beta_t$ whose trend the planner lowers by a lockdown effort $\xi_t\in[0,L]$ (progressively measurable):

$$dS_t=-\beta_tS_tI_t\,dt,\qquad dI_t=(\beta_tS_t-\alpha)I_t\,dt,\qquad d\beta_t=b(\beta_t,\xi_t)\,dt+\sigma(\beta_t)\,dW_t .$$

Here $\beta$ stays in an open interval $\mathcal I\subset(0,\infty)$, and $b$, $\sigma>0$ are bounded and smooth in $\beta$ with bounded derivatives of all orders. A typical choice is the mean-reverting diffusion $d\beta_t=\vartheta(\hat\beta(L-\xi_t)-\beta_t)dt+\sigma\beta_t(\gamma-\beta_t)dW_t$ on $(0,\gamma)$. A vaccine arrives at an independent exponential time with rate $\lambda_o$; the social cost rate $C(I,\xi)$ is convex, nondecreasing in both arguments, Lipschitz and semiconcave in $I$. With $\lambda=\lambda_o+\delta$ ($\delta$ the discount rate) the problem is

$$V(x,y,z)=\inf_{\xi}\ \mathbb E\Bigl[\int_0^\infty e^{-\lambda t}C(I_t,\xi_t)\,dt\Bigr],\qquad (S_0,I_0,\beta_0)=(x,y,z)\in\mathcal O .$$

**Theorem.**

1. $V$ is bounded, Lipschitz and semiconcave on $\mathcal O$, and it is a viscosity solution of the HJB equation

$$\lambda V=-zxy\,V_x+(zx-\alpha)y\,V_y+\tfrac12\sigma(z)^2V_{zz}+\min_{\xi\in[0,L]}\bigl\{C(y,\xi)+b(z,\xi)V_z\bigr\}.$$

2. $V_z$ exists and is continuous, and in fact $V\in C^2(\mathcal O)$ solves the HJB equation classically, despite the degeneracy (noise acts only on $\beta$).
3. *(Verification.)* The feedback

$$\hat\xi(x,y,z)\in\operatorname*{arg\,min}_{\xi\in[0,L]}\bigl\{C(y,\xi)+b(z,\xi)V_z(x,y,z)\bigr\}$$

is optimal whenever the closed-loop system admits a unique strong solution.

In the mean-reverting case study the optimal policy numerically has three phases: the epidemic first runs freely, is then vigorously tamed, and finally a less stringent containment is kept. After a certain date the product $\frac{\beta_t}{\alpha}S_t$ stays strictly below one while the reproduction number $\beta_t/\alpha$ itself oscillates above one, and larger fluctuations $\sigma$ make the lockdown start earlier and spread over a longer period.

## Expansion

Boundedness and Lipschitz continuity come from the bounded cost and the Lipschitz flow of the SIR system in its initial data; semiconcavity follows from semiconcavity of $C(\cdot,\xi)$ and smooth dependence of the state on $(x,y,z)$, and dynamic programming gives the viscosity property. The key step is $C^1$ regularity in $z$: a semiconcave function with a convex kink in $z$ would admit smooth test functions touching from above with $\varphi_{zz}\to-\infty$, contradicting the viscosity subsolution inequality because $\sigma>0$. With $V_z$ continuous, the $\min$ term is a known continuous function, and the transition density of the uncontrolled process (which satisfies Gaussian bounds by Hörmander-type hypoellipticity) upgrades $V$ to a classical $C^2$ solution, after which a standard verification argument applies.

## Sources

- Salvatore Federico, Giorgio Ferrari, "Taming the spread of an epidemic by lockdown policies", Journal of Mathematical Economics 93 (2021), 102453, <https://doi.org/10.1016/j.jmateco.2020.102453>. Published version of arXiv:2007.10870, cited next; locators there refer to the arXiv version.
- S. Federico, G. Ferrari, "Taming the spread of an epidemics by lockdown policies", arXiv:2007.10870 (2020), Section 2 (model, Assumptions 2.1 and 2.4, the planner problem), Section 3 (Propositions 3.1–3.2, Theorem 3.3), Appendix (Lemma A.1, Propositions A.2–A.3) and the numerical study. <https://doi.org/10.48550/arXiv.2007.10870>
