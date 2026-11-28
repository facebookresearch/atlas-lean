# Endemic equilibrium of the age-structured dengue model as a scalar fixed point

**Model.** In an age-structured host–vector model of dengue (SIS hosts structured by age $x \in [0,A]$, uninfected/infected vectors), the vector compartment is replaced by its quasi-equilibrium. Let $p(x)$ be the host age distribution with $\frac1N\int_0^Ap = 1$, $w(x) = i(x)/p(x)$ the infected fraction at age $x$, $\gamma > 0$ the recovery rate, and $\theta(x) > 0$ the continuous age-dependent effective transmission rate. The equilibrium age profile of infection then solves

$$ w'(x) = -\gamma w + \theta(x)\,(1 - w)\,Q(w), \quad w(0) = 0, \qquad Q(w) = \frac1N\int_0^A p(y)\,w(y)\,dy, $$

where $Q$ is the overall infected fraction that drives the force of infection through the vectors.

**Reduction.** With $\Lambda(x,s) = \int_s^x\theta$, $k(x,s) = \frac{p(x)}{N}\theta(s)e^{-\gamma(x-s)}$ on the triangle $\Omega = \{0 \le s \le x \le A\}$ and $\theta_{\max} = \max\theta$, the solution for given $Q$ is $w(x;Q) = Qe^{-\gamma x}\int_0^xe^{\gamma s}\theta(s)e^{-Q\Lambda(x,s)}\,ds$. Equilibria are exactly the solutions of the scalar equation

$$ Q = Q\iint_\Omega k(x,s)\,e^{-Q\Lambda(x,s)}\,d(s,x), $$

and the **basic reproductive number** is $\mathcal{R}_0 = \iint_\Omega k(x,s)\,d(s,x)$.

**Theorem.**

*(1)* For $Q > 0$ the profile satisfies $0 < w(x;Q) < 1$ for $x > 0$, $w(0) = 0$, and necessarily $Q < 1$.

*(2)* If $0 < \mathcal{R}_0 \le 1$, only the disease-free solution $Q = 0$ exists. If $\mathcal{R}_0 > 1$, there is additionally a unique endemic solution $Q^* \in (0,1)$, and

$$ 0 < Q^* < \frac{\mathcal{R}_0 - 1}{\frac{\gamma}{\gamma + \theta_{\max}} + \mathcal{R}_0 - 1} \longrightarrow 0 \quad (\mathcal{R}_0 \to 1^+). $$

*(3)* The iteration $Q^{(j)} = T(Q^{(j-1)}) := Q^{(j-1)}\iint_\Omega k\,e^{-Q^{(j-1)}\Lambda}$ has $T'(0) = \mathcal{R}_0$. For $\mathcal{R}_0 < 1$ it converges locally to $0$. For $1 < \mathcal{R}_0 < 2e \approx 5.44$, $|T'(Q^*)| < 1$, so it converges locally to the endemic $Q^*$ while $Q = 0$ is repelling.

Fitting a Gaussian-peaked $\theta(x) = \theta_0 + \theta_1e^{-(x-x_p)^2/(2\sigma^2)}$ to hospitalization data from Semarang, Indonesia reproduces the observed concentration of cases in young age groups.

## Expansion

Write $F(Q) = 1 - \iint_\Omega k\,e^{-Q\Lambda}$, so nonzero equilibria solve $F(Q) = 0$. Then $F(0) = 1 - \mathcal{R}_0$, $F(1) > \gamma/(\gamma + \theta_{\max}) > 0$, and $F' = \iint k\Lambda e^{-Q\Lambda} \ge 0$. Hence $F$ is nondecreasing and has a root in $(0,1)$ exactly when $\mathcal{R}_0 > 1$; strict monotonicity on $(0,1]$ makes it unique. The bound $F'(Q) < \mathcal{R}_0e^{-1}/Q$ (from $ue^{-u} \le e^{-1}$) controls $T'(Q^*) = 1 - Q^*F'(Q^*)$, which gives the contraction condition $\mathcal{R}_0 < 2e$.

## Sources

- N. C. Ganegoda, T. Götz and K. P. Wijaya, "An Age-Dependent Model for Dengue Transmission: Analysis and Comparison to Field Data from Semarang, Indonesia", arXiv:1908.09256 (2019), Section 2 (model reduction), Section 3 (Lemmas 1–5, Theorem 6 on existence of solutions, Theorem 7, Lemmas 8–9, Theorem 10), Section 4 (parameter estimation), <https://doi.org/10.48550/arXiv.1908.09256>.
