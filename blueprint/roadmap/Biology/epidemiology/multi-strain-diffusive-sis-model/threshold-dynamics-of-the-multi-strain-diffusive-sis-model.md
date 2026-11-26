# Threshold dynamics of the multi-strain diffusive SIS model

Let $\Omega \subset \mathbb R^n$ be a bounded domain with smooth boundary and outer normal $\vec n$. The multi-strain diffusive SIS model with $k$ strains and no co-infection is

$$\begin{aligned} \partial_t S &= d_S \Delta S + \sum_{i=1}^k \gamma_i I_i - \frac{S \sum_{i=1}^k \beta_i I_i}{S + \sum_{j=1}^k I_j}, \\ \partial_t I_i &= d_i \Delta I_i - \gamma_i I_i + \frac{\beta_i S I_i}{S + \sum_{j=1}^k I_j}, \qquad i = 1, \dots, k, \end{aligned}$$

in $\Omega \times (0, \infty)$, with $\partial_{\vec n} S = \partial_{\vec n} I_i = 0$ on $\partial\Omega$, positive Hölder continuous transmission and recovery rates $\beta_i, \gamma_i$ on $\overline\Omega$, diffusion rates $d_S \ge 0$, $d_i > 0$, and nonnegative initial data of total mass $N = \int_\Omega (S + \sum_i I_i)\,dx > 0$, which is conserved.

For each strain define the basic reproduction number of the single-strain problem,

$$R_{0,i} = \sup\Bigl\{ \frac{\int_\Omega \beta_i \varphi^2}{\int_\Omega \bigl(d_i |\nabla\varphi|^2 + \gamma_i \varphi^2\bigr)} : \varphi \in H^1(\Omega) \setminus \{0\} \Bigr\}, \qquad R_0 = \max_i R_{0,i}.$$

**Theorem.** Let $k \ge 2$, $d_S > 0$, and let $(S, I_1, \dots, I_k)$ be a classical solution with positive initial data.

1. If $R_{0,i} \le 1$ for some $i$, then $\|I_i(t, \cdot)\|_\infty \to 0$.
2. If $R_0 \le 1$, then $\|S(t, \cdot) - N/|\Omega|\|_\infty + \sum_i \|I_i(t, \cdot)\|_\infty \to 0$: the solution converges to the unique disease-free equilibrium.
3. If $R_0 > 1$, there is $m^* > 0$, independent of the initial data, with $\liminf_{t \to \infty} \min_{x \in \overline\Omega} \sum_{i=1}^k I_i(t, x) \ge m^*$.

$R_0$ does not depend on $d_S$, so persistence or extinction of the disease is unaffected by the movement rate of susceptibles. For each $i$, $R_{0,i} \ge \int_\Omega \beta_i / \int_\Omega \gamma_i$, with equality if and only if $R_i = \beta_i/\gamma_i$ is constant.

## Expansion

$R_{0,i}$ is the principal eigenvalue characterization of the linearization of the $i$-th equation at the disease-free state $S = N/|\Omega|$ (where the incidence becomes $\beta_i I_i$); $R_{0,i} \le 1$ makes the principal eigenvalue of $d_i\Delta + \beta_i - \gamma_i$ nonpositive, and comparison with $\beta_i S/(S + \sum_j I_j) \le \beta_i$ gives extinction of strain $i$. Uniform persistence for $R_0 > 1$ follows from the instability of the disease-free equilibrium and dissipativity of the mass-conserving system. The lower bound on $R_{0,i}$ comes from the test function $\varphi \equiv 1$.

## Sources

- Y. Lou and R. B. Salako, *Control strategies for a multi-strain epidemic model*, Bull. Math. Biol. 84 (2022), 10, <https://doi.org/10.1007/s11538-021-00957-6>, PMCID PMC8627176 (Theorem 2.1; definition of $R_{0,i}$ in Section 2).
