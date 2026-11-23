# Monotone coupling of two measures

Let $E$ be a set and $\mu, \nu$ measures on $\{0,1\}^E$ (with its product σ-algebra). A measure $\kappa$ on $\{0,1\}^E \times \{0,1\}^E$ is a *monotone coupling* of $\mu$ and $\nu$ if

- its first marginal is $\mu$: $\kappa(A \times \{0,1\}^E) = \mu(A)$ for measurable $A$;
- its second marginal is $\nu$: $\kappa(\{0,1\}^E \times B) = \nu(B)$ for measurable $B$;
- it gives no mass to the pairs off the [order set](order-set.md): $\kappa(\{(\omega, \omega') : \omega \not\le \omega'\}) = 0$.
