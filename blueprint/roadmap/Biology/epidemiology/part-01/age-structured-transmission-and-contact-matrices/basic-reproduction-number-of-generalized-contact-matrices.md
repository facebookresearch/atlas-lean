# Basic reproduction number of generalized contact matrices

Consider an SEIR model on population groups $a = 1, \dots, T$ of sizes $N_a > 0$:

$$\dot S_a = -\Lambda_a S_a, \quad \dot E_a = \Lambda_a S_a - \Psi E_a, \quad \dot I_a = \Psi E_a - \Gamma I_a, \quad \dot R_a = \Gamma I_a, \qquad \Lambda_a = \Phi \sum_b G_{ab} \frac{I_b}{N_b},$$

where $G_{ab}$ is the mean number of contacts an individual of group $a$ has with group $b$ per unit time, $\Phi$ the transmissibility, $\Psi$ the rate of becoming infectious and $\Gamma$ the recovery rate. Groups may be indexed by age alone ($T = K$, matrix $C$) or by age together with further attributes such as socioeconomic status ($T = K V_1 \cdots V_m$, *generalized contact matrix* $G$, flattened to $T \times T$). Write $N_G = \mathrm{diag}(N_a)$ and $R_G = N_G G$ for the matrix of total contacts between groups, which is symmetric by reciprocity.

1. **Reproduction number.** By the next-generation matrix method,

    $$\mathcal R_0 = \frac{\Phi}{\Gamma}\, \rho(\tilde G), \qquad \tilde G_{ab} = G_{ab}\, \frac{N_a}{N_b}, \quad\text{i.e.}\quad \tilde G = R_G N_G^{-1},$$

    and likewise $\mathcal R_0 = (\Phi/\Gamma)\rho(\tilde C)$ with $\tilde C = R N^{-1}$ for an age-only matrix.
    2. **Monotonicity under stratification.** Let $\tilde C = R N^{-1} \in \mathbb R^{K \times K}$ with $R$ symmetric nonnegative and $N$ positive diagonal, and let $\tilde G = R_G N_G^{-1} \in \mathbb R^{K V_1 \times K V_1}$ with $R_G$ symmetric nonnegative and $N_G$ positive diagonal be a refinement by one more attribute, i.e.

    $$\sum_{\alpha, \beta = 1}^{V_1} (R_G)_{i\alpha, j\beta} = R_{ij}, \qquad \sum_{\alpha, \beta = 1}^{V_1} (N_G)_{i\alpha, j\beta} = N_{ij}.$$

Then $\rho(\tilde G) \ge \rho(\tilde C)$. Iterating, adding attributes never decreases $\mathcal R_0$. Equality holds under random mixing across the added attribute, i.e. when contacts are proportional to the product of subgroup sizes.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

$\tilde C = R N^{-1}$ is similar to the symmetric matrix $N^{-1/2} R N^{-1/2}$, so it has real spectrum, and by Perron–Frobenius its spectral radius is its largest eigenvalue. By the Rayleigh principle,

$$\rho(\tilde C) = \max_{x \ne 0} \frac{x^{\mathsf T} R\, x}{x^{\mathsf T} N x}, \qquad \rho(\tilde G) = \max_{y \ne 0} \frac{y^{\mathsf T} R_G\, y}{y^{\mathsf T} N_G\, y}.$$

Lifting any $x \in \mathbb R^K$ to $y_{i\alpha} = x_i$ gives $y^{\mathsf T} R_G y = \sum_{i,j} x_i x_j \sum_{\alpha,\beta} (R_G)_{i\alpha, j\beta} = x^{\mathsf T} R x$ and $y^{\mathsf T} N_G y = x^{\mathsf T} N x$. So every quotient available for $\tilde C$ is also available for $\tilde G$, and the maximum can only grow. Aggregating contacts over an attribute therefore underestimates the epidemic threshold whenever mixing across that attribute is assortative. In survey data stratified by age and socioeconomic status, the generalized matrices changed both $\mathcal R_0$ and how the attack rate was distributed across socioeconomic groups.

## Sources

- A. Manna, L. Dall'Amico, M. Tizzoni, M. Karsai, N. Perra, "Generalized contact matrices allow integrating socioeconomic variables into epidemic models", *Science Advances* (2024), Results ("Generalized contact matrices", "Epidemic model" Eq. (1), "Spectral properties of generalized contact matrices and the basic reproductive number", Theorem 1 and the random-mixing corollary), <https://doi.org/10.1126/sciadv.adk4606> (PMC11468902).
