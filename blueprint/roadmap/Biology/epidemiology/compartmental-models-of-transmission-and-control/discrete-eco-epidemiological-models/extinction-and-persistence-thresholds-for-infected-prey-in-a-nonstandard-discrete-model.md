# Extinction and persistence thresholds for infected prey in a nonstandard discrete model

**Model.** Discretizing a nonautonomous predator–prey model with disease in the prey by Mickens' nonstandard finite-difference method gives, for susceptible prey $S_n$, infected prey $I_n$ and predators $P_n$,

$$\begin{aligned}
S_{n+1}-S_n &= \Lambda_n - \mu_nS_{n+1} - a_n f(S_{n+1},I_n,P_n)P_n - \beta_nS_{n+1}I_n,\\
I_{n+1}-I_n &= \beta_nS_{n+1}I_n - \eta_n g(S_n,I_n,P_n)I_{n+1} - c_nI_{n+1},\\
P_{n+1}-P_n &= (r_n - b_nP_{n+1})P_n + \gamma_na_n f(S_{n+1},I_n,P_n)P_n + \theta_n\eta_n g(S_n,I_n,P_n)I_{n+1},
\end{aligned}$$

under the source's standing hypotheses H1)–H7):
- H1) the sequences $(\Lambda_n),(a_n),(\beta_n),(\eta_n),(c_n),(r_n),(b_n),(\gamma_n),(\theta_n)$ are bounded and nonnegative, and $0<\mu_n\le c_n$;
- H2) $(\Lambda_n)$, $(r_n)$, $(b_n)$ are bounded away from $0$;
- H3) the predation functional responses $f$ (on susceptible prey) and $g$ (on infected prey) are nonnegative $C^1$ functions on $(\mathbb R^+_0)^3$; for fixed $x,z>0$, $y\mapsto f(x,y,z)$ and $y\mapsto g(x,y,z)$ are nonincreasing; for fixed $y,z>0$, $x\mapsto f(x,y,z)$ is nondecreasing and $x\mapsto g(x,y,z)$ is nonincreasing; for fixed $x,y>0$, $z\mapsto g(x,y,z)$ is nondecreasing and $z\mapsto f(x,y,z)$ is nonincreasing (the source prints $g$ in both of these last two clauses; read literally they would force $g$ to be constant in $z$, which excludes the case $g=g_0(S,I)P$ used below);
- H4) there is $\omega\in\mathbb N$ with $\limsup_{n\to\infty}\prod_{k=n}^{n+\omega}\frac{1}{1+\mu_k}<1$;
- H5) for every $p$ and every initial condition $(S_p,I_p,P_p)\in(\mathbb R^+_0)^3$ the system has a unique solution for $n\ge p$;
- H6) solutions with nonnegative (resp. positive) initial conditions stay nonnegative (resp. positive);
- H7) each solution with positive initial condition is bounded, and there is a bounded region $\mathcal R$ that contains the $\omega$-limit of all solutions with positive initial conditions.

**Thresholds.** Let $s^*_n$ solve the prey-only equation $s_{n+1} = (\Lambda_n + s_n)/(1+\mu_n)$, $y^*_n$ the predator-only logistic equation $y_{n+1} = (r_n+1)y_n/(1+b_ny_n)$, and $(x^*_n,z^*_n)$ the globally attracting solution of the disease-free predator–prey subsystem (the $\varepsilon=0$ member of the family in the source's hypothesis H8)). For $\lambda \in \mathbb N$ define

$$\mathcal R^u(\lambda) = \limsup_{n\to\infty}\prod_{k=n}^{n+\lambda}\frac{1+\beta_ks^*_{k+1}}{1+c_k+\eta_k g(s^*_k,0,y^*_k)}, \qquad \mathcal R^\ell(\lambda) = \liminf_{n\to\infty}\prod_{k=n}^{n+\lambda}\frac{1+\beta_kx^*_{k+1}}{1+c_k+\eta_k g(x^*_k,0,z^*_k)},$$

which, under H1)–H4), do not depend on the chosen positive solutions.

**Theorem (extinction).** If $g(S+I,0,P) \le g(S,I,P)$ and $\mathcal R^u(\lambda) < 1$ for some $\lambda$, the infected prey go extinct. If moreover $a \equiv 0$ (no predation on susceptible prey) and $g(S,I,P) = g_0(S,I)P$, every disease-free solution is globally attractive.

**Theorem (persistence).** If $\mathcal R^\ell(\lambda) > 1$ for some $\lambda$, and the auxiliary perturbed disease-free subsystems have continuous (in the perturbation $\varepsilon$) families of globally asymptotically stable nonnegative solutions (the source's H8)–H9)), the infected prey are strongly persistent: $\liminf_n I_n > 0$.

For periodic coefficients the thresholds reduce to products over one period, $\mathcal R^u_{\rm PER}<1$ giving extinction and $\mathcal R^\ell_{\rm PER}>1$ giving persistence together with a periodic orbit; in the autonomous case they reduce to single-step ratios $\mathcal R^u_A$ and $\mathcal R^\ell_A$.

## Expansion

From the $I$ equation, $I_{n+1} = I_n\,\frac{1+\beta_nS_{n+1}}{1+c_n+\eta_n g(S_n,I_n,P_n)}$, so infected prey grow multiplicatively by the factor appearing in the thresholds. Upper solutions use the largest possible prey level ($s^*$, no predation or disease) and the smallest predation pressure from predators at their disease-free logistic level, giving the extinction condition; persistence compares with the disease-free predator–prey attractor $(x^*,z^*)$ and uses continuity in the small perturbation $\varepsilon$ of the auxiliary systems to show that $I$ cannot stay near $0$.

## Sources

- Lopo F. de Jesus, César M. Silva and Helder Vilarinho, "Dynamics of a discrete eco-epidemiological model with disease in the prey", arXiv:2007.10279 (2020), Theorems 1 and 2 (extinction and strong persistence), Theorems 3 and 4 (variant model), Corollaries 1–4 (periodic and autonomous cases), <https://doi.org/10.48550/arXiv.2007.10279>.
