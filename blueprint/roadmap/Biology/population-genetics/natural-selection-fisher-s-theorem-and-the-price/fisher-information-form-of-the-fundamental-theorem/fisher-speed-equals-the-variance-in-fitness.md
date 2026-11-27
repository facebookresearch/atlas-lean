# Fisher speed equals the variance in fitness

Under the hypotheses of the [partial-change theorem](partial-change-theorem-for-lotka-volterra-replicators.md), equip the interior of the simplex $\Delta^{n-1}$ with the Fisher information (Shahshahani) metric

$$g_p(v, w) = \sum_{i=1}^n \frac{v_i w_i}{p_i}, \qquad \sum_i v_i = \sum_i w_i = 0.$$

Then the squared Fisher speed of the frequency curve $p(t)$ equals the variance in fitness:

$$g_{p(t)}\bigl(\dot p(t), \dot p(t)\bigr) = \sum_{i=1}^n \frac{\dot p_i(t)^2}{p_i(t)} = \operatorname{Var}\bigl(f(P(t))\bigr).$$

Since the relative information $I(q, p) = \sum_i q_i \ln(q_i/p_i)$ satisfies $\frac{d}{dt}I(p(t), p(t_0))|_{t=t_0} = 0$ and $\frac{d^2}{dt^2}I(p(t), p(t_0))|_{t=t_0} = g(\dot p(t_0), \dot p(t_0))$, the variance in fitness is the rate at which information is updated, to second order, as the population evolves. The statement holds for arbitrary fitness functions, and in fact for any autonomous system $\dot P_i = F_i(P)$ with positive solutions, by setting $f_i = F_i/P_i$.

## Depends on

- [Partial-change theorem for Lotka–Volterra replicators](partial-change-theorem-for-lotka-volterra-replicators.md)
- [Kullback–Leibler divergence on a finite space](../../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/to-real-kl-div-eq-sum.md)

## Expansion

Substitute the replicator equation $\dot p_i = (f_i - \bar f)p_i$ into $\sum_i \dot p_i^2/p_i$ to get $\sum_i (f_i - \bar f)^2 p_i$. The second-derivative identity is the classical fact that the Hessian of relative entropy at the diagonal is the Fisher metric. Unlike the version for mean fitness, this form needs no assumption that the fitness functions are constant: variance in fitness need not cause progress, but it always causes change, measured in information.

## Sources

- J. C. Baez, "The fundamental theorem of natural selection", Entropy 23 (2021) 1436, <https://doi.org/10.3390/e23111436>, PMCID PMC8624378. Section 3, Theorem 2.
