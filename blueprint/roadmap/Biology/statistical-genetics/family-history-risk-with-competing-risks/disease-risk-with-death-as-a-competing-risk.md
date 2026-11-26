# Disease risk with death as a competing risk

Let an individual have [posterior disease hazard](posterior-survival-and-hazard-of-a-possible-carrier.md) $\lambda_\alpha(t)$ and death hazard $\lambda_{\mathrm{death}}(t)$ for $t \ge \tau$, and let $T^*$ be the earlier of disease onset and death. Death precludes disease, so the probability of developing the disease is the cumulative incidence

$$P(\text{disease by } t) = \int_\tau^t \lambda_\alpha(u)\,S_\beta(u)\,du, \qquad S_\beta(u) = \exp\Bigl(-\int_\tau^u \beta(s)\,ds\Bigr), \quad \beta = \lambda_\alpha + \lambda_{\mathrm{death}},$$

where $S_\beta$ is the probability of being alive and disease-free at age $u$. If $\lambda_\alpha$ and $\beta$ are constant, equal to $\alpha_j$ and $\beta_j > 0$, on each interval $(c_{j-1}, c_j]$ of a grid $\tau = c_0 < c_1 < \dots < c_N$, then for $t \in (c_{j-1}, c_j]$

$$\int_{c_{j-1}}^t \lambda_\alpha(u)\,S_\beta(u)\,du = \frac{\alpha_j}{\beta_j}\bigl(S_\beta(c_{j-1}) - S_\beta(t)\bigr),$$

so the risk by $c_k$ is the sum $\sum_{j \le k} (\alpha_j/\beta_j)(S_\beta(c_{j-1}) - S_\beta(c_j))$ with $S_\beta(c_j) = S_\beta(c_{j-1})e^{-\beta_j(c_j - c_{j-1})}$.

## Depends on

- [Posterior survival and hazard of a possible carrier](posterior-survival-and-hazard-of-a-possible-carrier.md)

## Expansion

Disease occurs in $(u, u + du)$ before death iff the individual is alive and disease-free at $u$ and the disease event occurs then, which has probability $S_\beta(u)\lambda_\alpha(u)\,du$. On an interval with constant hazards $S_\beta(u) = S_\beta(c_{j-1})e^{-\beta_j(u - c_{j-1})}$, and integrating the exponential gives the closed form. Ignoring death (using $1 - S(t)$ alone) overstates lifetime risk, markedly so at older ages.

## Sources

- G. Nuel, A. Lefebvre and O. Bouaziz, "Computing individual risks based on family history in genetic disease in the presence of competing risks", Computational and Mathematical Methods in Medicine 2017 (2017) 9193630, <https://doi.org/10.1155/2017/9193630>, PMCID PMC5700554. Section 2.3, Lemma 3 (Equation (12)) and the step-by-step computation that follows it.
