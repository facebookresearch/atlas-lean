# Basic reproduction number of the age-structured SEQIR model

**Model.** Let $U(a)$ be the stationary age density of a population with age-specific mortality $\mu(a)$, with $\int_0^\infty\mu = \infty$. Write $s, e, q, i, r$ for the age-specific fractions of susceptible, exposed, quarantined, infectious and recovered individuals. Along cohorts (time and age advancing together):

$$\begin{aligned} (\partial_t + \partial_a)s &= -\phi(a,t)s, &\quad (\partial_t + \partial_a)e &= \phi s - (\mu_1 + q_1)e,\\ (\partial_t + \partial_a)q &= q_1e - (\gamma_1 + \gamma_2)q, &\quad (\partial_t + \partial_a)i &= \mu_1e + \gamma_1q - \gamma i, \end{aligned}$$

with $s(0,t) = 1$. Here exposed individuals develop symptoms at rate $\mu_1$ or are quarantined at rate $q_1$, quarantined individuals become infectious at rate $\gamma_1$ or recover at rate $\gamma_2$, and infectious individuals recover at rate $\gamma$. The force of infection is $\phi(a,t) = \int_0^\infty k(a,\sigma)U(\sigma)i(\sigma,t)\,d\sigma$, and mixing is separable, $k(a,b) = k_1(a)k_2(b)$.

**Theorem.**

1. (Reproduction number.) Endemic steady states correspond to $\phi(a) = hk_1(a)$ with $h > 0$ solving $F(h) = 1$, where $F$ is an explicit functional of $h$. The basic reproduction number is $R_0 = F(0) = \mathcal R_1 + \mathcal R_2$, the sum of the contributions through direct progression $E \to I$ and through quarantine $E \to Q \to I$:

$$\mathcal R_1 = \int_0^\infty k_2(b)U(b)e^{-\gamma b}\int_0^b\mu_1e^{(\gamma - \mu_1 - q_1)\sigma}\int_0^\sigma k_1(y)e^{(\mu_1+q_1)y}\,dy\,d\sigma\,db,$$

$$\mathcal R_2 = \int_0^\infty k_2(x)U(x)e^{-\gamma x}\int_0^x\gamma_1e^{(\gamma - \gamma_1 - \gamma_2)y}\int_0^yq_1e^{(\gamma_1 + \gamma_2 - \mu_1 - q_1)z}\int_0^zk_1(a)e^{(\mu_1+q_1)a}\,da\,dz\,dy\,dx .$$

2. (Disease elimination.) The functional $V = \int_0^\infty[\alpha_1(a)e + \alpha_2(a)q + \alpha_3(a)i]\,da$, with weights $\alpha_3(a) = \int_a^\infty k_2(x)U(x)e^{\gamma(a-x)}dx$, $\alpha_2(a) = \int_a^\infty\gamma_1\alpha_3(z)e^{(\gamma_1+\gamma_2)(a-z)}dz$ and $\alpha_1(a) = \int_a^\infty(q_1\alpha_2 + \mu_1\alpha_3)(z)\,e^{(\mu_1+q_1)(a-z)}dz$, satisfies

$$\dot V \le (R_0 - 1)\int_0^\infty k_2(b)\,i(b,t)\,U(b)\,db .$$

The source prints this bound, (3.22) and (3.30), with $k_1(b)$ in place of $k_2(b)$; its own (3.20)–(3.21), $\alpha_3'-\gamma\alpha_3=-k_2U$ and $\phi=k_1\int k_2Ui$, give $\dot V=\bigl(\int_0^\infty\alpha_1sk_1\,da-1\bigr)\int_0^\infty k_2(b)i(b,t)U(b)\,db$, so the page corrects the weight to $k_2$. Hence the disease-free state attracts all solutions when $R_0 \le 1$.

3. (Constant mortality and homogeneous mixing.) If $\mu(a) \equiv \mu$, so $U(a) = \mu e^{-\mu a}$, and $k_1 \equiv 1$, $k_2$ constant, then

$$R_0 = \frac{k_2\,\mu_1}{(\mu + \gamma)(\mu + \mu_1 + q_1)} + \frac{k_2\,\gamma_1q_1}{(\mu + \gamma)(\mu + \gamma_1 + \gamma_2)(\mu + \mu_1 + q_1)},$$

which reduces to $k_2\mu_1/((\mu+\gamma)(\mu+\mu_1))$ without quarantine.

4. (Optimal vaccination.) For the corresponding SEIR model with age-specific vaccination $v(a)$ and no quarantine, consider minimizing the vaccination cost (4.6) of the source over vaccination strategies subject to an upper bound on the weighted prevalence $\int_0^\infty f(a)I(a)\,da$ and to the constraint (4.8), $\tilde H(v)=h$, which fixes the level $h$ of $\int_0^\infty k_2(a)I(a)\,da$ (the source uses these constraints "instead of considering basic reproduction number"). This problem has an optimal strategy that vaccinates at most three ages: $v(a) = c_1\delta_{A_1}(a) + c_2\delta_{A_2}(a) + c_3\delta_{A_3}(a)$ with $0 \le A_1 < A_2 < A_3$. If all $c_j \ne 0$, every remaining susceptible is vaccinated at age $A_3$.

## Expansion

Integrating the steady-state cohort ODEs gives $s(a) = e^{-\int_0^a\phi}$ and convolution formulas for $e, q, i$. Substituting into $\phi(a) = hk_1(a)$ and dividing by $h$ yields $F(h) = 1$. At $h = 0$, $F(0)$ is the expected weighted number of secondary infections produced by one infection, summed over the two routes to the infectious class. The Lyapunov weights solve the adjoint (backward) equations, so that the $e$ and $q$ terms in $\dot V$ cancel. Comparing with $R_0$ after exchanging the order of integration, with $s \le 1$, gives the inequality. With constant rates, each route contributes a product of competing-risk probabilities and the mean infectious period $1/(\mu + \gamma)$. The optimal vaccination problem is linear in the distribution of vaccination ages, so a Carathéodory-type argument over the constraint set gives optimizers supported on at most three ages.

## Sources

- Manoj Kumar, Syed Abbas, "Analysis of steady state solutions to an age structured SEQIR model with optimal vaccination", arXiv (2020). Section "Model Formulation", Section "Steady state solutions" (formula for $R_0$, Lyapunov functional, subsections "Average Age of Infection" and "Negative Exponential Survival"), Section "Optimal Vaccination" (final proposition). <https://doi.org/10.48550/arXiv.2012.10068>. Published version: Mathematical Methods in the Applied Sciences 45(17) (2022), 10718–10735, <https://doi.org/10.1002/mma.8414>; locators above refer to the arXiv version.
