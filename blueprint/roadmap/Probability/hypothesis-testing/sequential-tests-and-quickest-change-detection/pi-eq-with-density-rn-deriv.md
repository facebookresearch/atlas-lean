# Density of a finite product of absolutely continuous laws

Let $P_0$ and $P_1$ be probability measures on a measurable space $\mathcal{X}$ with $P_1 \ll P_0$, and let $\iota$ be a finite set. Then the product law $P_1^{\otimes \iota}$ has density

$$x \mapsto \prod_{i \in \iota} \frac{dP_1}{dP_0}(x_i)$$

with respect to $P_0^{\otimes \iota}$: the likelihood ratio of $|\iota|$ independent observations, as in the integrals of Wald's inequalities (Encyclopedia of Mathematics, *Sequential probability ratio test*, equations (a1)–(a2)).

The proof checks the identity on boxes $\prod_i s_i$, where the integral of $\prod_i (dP_1/dP_0)(x_i)$ factorises because the coordinates are independent under $P_0^\iota$, and each factor is $\int_{s_i} dP_1/dP_0 \, dP_0 = P_1(s_i)$.

## Sources

- B. Eisenberg, *Sequential probability ratio test*, Encyclopedia of Mathematics (online), equations (a1)–(a3), equation (a1) (the likelihood ratio of $n$ independent observations).
