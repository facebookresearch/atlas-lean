# Control reproduction number of an age-stratified RSV model with infant prophylaxis

**Model.** A population with recruitment $\Lambda$ is split into three age classes (infants, children, older individuals) with an 11-compartment SIR structure. Newborns are protected by a long-acting monoclonal antibody at birth with coverage $p$ (compartment $P$, relative susceptibility $\sigma$) or enter the unprotected infant susceptible classes $S_{1e}, S_{1w}$; infants can also receive catch-up prophylaxis. Age classes mature at rates $\eta_i$ and die at rates $\mu_i$, transmission from age class $j$ to $i$ has rate $\beta_{ij}$, and $\xi_i$ is the total exit rate from infection in class $i$. At the disease-free equilibrium (DFE) let $A_{ij}$ be the effective transmission coefficients, e.g. $A_{11} = \beta_{11}(\sigma P^0 + S^0_{1e} + S^0_{1w})$, $A_{12} = \beta_{12}(\sigma P^0 + S^0_{1e} + S^0_{1w})$, $A_{21} = \beta_{21} S^0_2$.

**Theorem.**
1. The region $\Omega = \{\mathbf x \in \mathbb R^{11}_+ : \sum_i x_i \le \Lambda/\min\{\mu_1, \mu_2, \mu_3\}\}$ is positively invariant and globally attracting.
2. The control reproduction number is

$$\mathcal R_c = \max\{\mathcal R_c^{(1,2)}, \mathcal R_c^{(3)}\}, \qquad \mathcal R_c^{(3)} = \frac{\beta_{33} S_3^0}{\xi_3},$$

where $\mathcal R_c^{(1,2)}$ is the spectral radius of the $2 \times 2$ next-generation block coupling infants and children, given in closed form in terms of $A_{11}/\xi_1$, $A_{22}/\xi_2$, $A_{12}$, $A_{21}$ and the maturation rate $\eta_1$.
3. If $\mathcal R_c < 1$ the DFE is locally asymptotically stable; if $\mathcal R_c > 1$ the system is uniformly persistent.

## Expansion

The next-generation matrix at the DFE is block structured, with the oldest class forming its own block, so its spectral radius is the larger of the two block radii. Prophylaxis enters $\mathcal R_c$ only through the infant susceptible pool $\sigma P^0 + S^0_{1e} + S^0_{1w}$, which shrinks as coverage at birth and catch-up coverage increase. For realistic Italian parameters, raising coverage strongly reduces infant incidence and gives indirect protection to older classes, while $\mathcal R_c$ may remain above one, because transmission among older age classes sustains circulation.

## Sources

- A. Autoriello, S. Averga, B. Buonomo, R. Della Marca, "Impact of Nirsevimab prophylaxis on RSV dynamics: a stage-structured modelling study", arXiv:2607.08344 (2026), Propositions 1, 2 and 3 and the control reproduction number (Section 3), <https://doi.org/10.48550/arXiv.2607.08344>.
