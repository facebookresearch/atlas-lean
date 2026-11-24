# Likelihood-ratio change of measure on the first $n$ observations

Let $P_0$ and $P_1$ be probability measures on a measurable space $\mathcal{X}$ with $P_1 \ll P_0$, let $n \in \mathbb{N}$ and let $A \subseteq \mathcal{X}^{\mathbb{N}}$ be an event that depends only on the observations $X_1, \dots, X_n$ (that is, $A \in \mathcal{F}_n$, the [observation σ-algebra](observation-filtration.md)). Then

$$P_1^{\otimes \mathbb{N}}(A) = \int_A \prod_{i=1}^{n} \frac{dP_1}{dP_0}(X_i) \, dP_0^{\otimes \mathbb{N}}:$$

the likelihood ratio $R_n$ is the density of $P_1^{\otimes \mathbb{N}}$ with respect to $P_0^{\otimes \mathbb{N}}$ on $\sigma(X_1, \dots, X_n)$. This is the change of measure behind Wald's inequalities (Encyclopedia of Mathematics, *Sequential probability ratio test*, equation (a2)).

The event is the preimage of a set $B$ of the first $n$ coordinates; the law of those coordinates under $P_i^{\mathbb N}$ is the finite product $P_i^n$, and $P_1^n$ has density $\prod_{i<n} dP_1/dP_0$ with respect to $P_0^n$.

## Sources

- B. Eisenberg, *Sequential probability ratio test*, Encyclopedia of Mathematics (online), equations (a1)–(a3), equation (a2) (the integrals $\int \lambda_N \, dP_0$).

## Informally uses

- [Density of a finite product of absolutely continuous laws](pi-eq-with-density-rn-deriv.md)
