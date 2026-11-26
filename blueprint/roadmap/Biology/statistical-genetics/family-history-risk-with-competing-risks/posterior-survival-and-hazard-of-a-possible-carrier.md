# Posterior survival and hazard of a possible carrier

Let the age at disease onset $T$ of an individual have survival function $S_1$ and hazard $\lambda_1$ if the individual carries the disease genotype, and $S_0$, $\lambda_0$ otherwise. Suppose the individual is disease-free at age $\tau$, and let $\pi$ be the posterior probability that the individual is a carrier given the family history (which includes being disease-free at $\tau$). Then for all $t \ge \tau$ the posterior survival and hazard are

$$S(t) = \pi\,\frac{S_1(t)}{S_1(\tau)} + (1 - \pi)\,\frac{S_0(t)}{S_0(\tau)},$$

$$\lambda(t) = \frac{1}{S(t)}\Bigl(\pi\,\frac{S_1(t)}{S_1(\tau)}\,\lambda_1(t) + (1 - \pi)\,\frac{S_0(t)}{S_0(\tau)}\,\lambda_0(t)\Bigr).$$

The posterior hazard is a mixture of the carrier and non-carrier hazards whose weights shift toward non-carriers with age, because carriers who remain unaffected become less likely. The probability $\pi$ is obtained exactly by forward–backward (belief propagation) recursions over a decomposition of the pedigree, which give the family-history likelihood and all individual posterior genotype probabilities in one pass.

## Expansion

Condition on the genotype: given carrier status the residual survival from $\tau$ is $S_1(t)/S_1(\tau)$, and the law of total probability with weights $\pi, 1 - \pi$ gives $S(t)$. The hazard is $-S'(t)/S(t)$, and $-\frac{d}{dt}S_g(t) = \lambda_g(t)S_g(t)$ gives the mixture form.

## Sources

- G. Nuel, A. Lefebvre and O. Bouaziz, "Computing individual risks based on family history in genetic disease in the presence of competing risks", Computational and Mathematical Methods in Medicine 2017 (2017) 9193630, <https://doi.org/10.1155/2017/9193630>, PMCID PMC5700554. Section 2.2, Theorem 1 (posterior genotype distribution by forward–backward recursions); Section 2.3, Theorem 2 (Equations (9)–(10)).
