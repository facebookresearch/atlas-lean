# Residual test for LWE secret candidates

A candidate secret $s'$ is checked on LWE samples by the spread of the centred residuals $b_i-a_i\cdot s'$: it is accepted when their sample standard deviation is at most a supplied threshold $\theta$. For a fixed candidate and fresh uniform samples, the residuals follow the centred error law when $s'=s$ and are exactly uniform when $s-s'$ has an invertible coordinate.

Let $(a_i,b_i)$, $i=1,\dots,N$ with $N\ge2$, satisfy $b_i\equiv a_i\cdot s+e_i\pmod q$, and let $s'$ be a candidate. Let $r_i\in(-q/2,q/2]$ be the centred representative of $b_i-a_i\cdot s' \bmod q$, and

$$
\sigma_{\mathrm{emp}}=\Bigl(\frac{1}{N-1}\sum_{i=1}^{N}(r_i-\bar r)^2\Bigr)^{1/2}.
$$

The test with threshold $\theta>0$, a supplied input, accepts $s'$ iff $\sigma_{\mathrm{emp}}\le\theta$. In the transformer attacks it runs on the original, unreduced samples, for example the $N=4n$ collected samples, with $\theta$ chosen between the two reference values below.

**Algebraic fact (always).** $b_i-a_i\cdot s'\equiv a_i\cdot(s-s')+e_i\pmod q$; in particular for $s'=s$ each $r_i$ is the centred representative of $e_i$, on any samples, reduced or not.

**Distributional facts (fixed candidate, fresh samples).** Condition on the secret $s$ and suppose $s'$ does not depend on the samples, the $a_i$ are independent and uniform on $\mathbb{Z}_q^n$, and the $e_i$ are independent with a common law on $\mathbb{Z}_q$ and independent of the $a_i$ (as for fresh samples of $\mathrm{LWE}(n,N,q,\chi_s,\chi_e)$ with error law $\chi_e$, conditional on $s$).

- If $s'=s$, the $r_i$ are independent and identically distributed with the law $\lambda_e$ of the centred representative of the common error law; let $\sigma_e$ be the standard deviation of $\lambda_e$ (for errors concentrated well inside $(-q/2,q/2)$ this is close to the error's standard deviation).
- If $s-s'$ has a coordinate invertible modulo $q$ (for instance $q$ prime and $s'\ne s$), the $r_i$ are independent and uniform on the $q$ integers of $(-q/2,q/2]$, whose variance is $(q^2-1)/12$.

A necessary condition for the test to separate the two cases is that $\lambda_e$ differ from the uniform law; if the error is itself uniform modulo $q$, both cases give the same residual law. The distributional facts do not carry over to a candidate chosen using the same samples, or to reduced samples, whose covariates are not uniform.

## Proof sketch

Uniformity: for a vector $d$ with an invertible coordinate, $x\mapsto x\cdot d$ is a surjective homomorphism $\mathbb{Z}_q^n\to\mathbb{Z}_q$ whose fibres all have $q^{n-1}$ elements, so it maps the uniform law to the uniform law; adding an independent $e_i$ preserves uniformity, and independence across $i$ follows from independent $(a_i,e_i)$. Any $q$ consecutive integers have variance $(q^2-1)/12$ under the uniform law. Li et al. (PICANTE, Appendix A.2) choose the threshold from confidence intervals for $\sigma_{\mathrm{emp}}$ based on the chi-square law of $(N-1)\sigma_{\mathrm{emp}}^2/\sigma^2$, which assumes Gaussian residuals, approximated by a normal law for $N>100$; that is a statistical heuristic.

## Expansion

A good expansion adds pages for:

- the pushforward of the uniform law on a finite abelian group under a surjective homomorphism is the uniform law.

## Depends on

- [LWE with a prescribed secret distribution](../small-and-sparse-secret-lwe/lwe-with-a-secret-distribution.md)

## Proof depends on

None.

## Sources

- Emily Wenger, Mingjie Chen, François Charton, Kristin Lauter, "SALSA: Attacking Lattice Cryptography with Transformers", Advances in Neural Information Processing Systems 35 (NeurIPS 2022); numbers from arXiv:2207.04785v2, Section 4.4.
- Cathy Yuanchen Li, Jana Sotáková, Emily Wenger, Mohamed Malhou, Evrard Garcelon, François Charton, Kristin Lauter, "SALSA PICANTE: a machine learning attack on LWE with binary secrets", ACM CCS 2023, https://doi.org/10.1145/3576915.3623076; numbers from arXiv:2303.04178v3, Section 4.3 (checking correctness) and Appendix A.2.
