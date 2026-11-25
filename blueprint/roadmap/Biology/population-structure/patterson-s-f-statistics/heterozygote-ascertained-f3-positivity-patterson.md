# Heterozygote ascertainment keeps f3 of an unadmixed target nonnegative

Let $A, B, C$ descend from a root $R$ along a tree with no admixture, with allele frequencies following the neutral Wright–Fisher diffusion on each edge,
whose transition kernel has the [Kimura series as its density](../../population-genetics/diffusion-theory/wright-fisher-diffusion/identification-of-the-kimura-series-with-the-neu.md). Count only sites polymorphic at $R$ (no back or recurrent mutation and no new mutation on
the edges below $R$), and weight the root frequency by $\mu_0(dr) = dr/r$ on $(0, 1)$, the mutation–drift equilibrium density of a derived allele. This measure
is σ-finite but has infinite total mass. Ascertaining one heterozygote in $A$ weights a site by $a(1 - a)$, and Patterson et al.'s equation (A1) defines

$$F_3^{\mathrm{het}}(C; A, B) = \frac{\int \mathbb E_r\bigl[(c - a)(c - b)\, a(1 - a)\bigr]\, \mu_0(dr)}{\int \mathbb E_r\bigl[a(1 - a)\bigr]\, \mu_0(dr)} .$$

The denominator is finite and positive, because $\mathbb E_r[a(1 - a)] = r(1 - r)\, e^{-\tau}$ with $\tau$ the diffusion length of the path from $R$ to $A$ (heterozygosity is an
[eigenfunction of the neutral generator](../../population-genetics/diffusion-theory/wright-fisher-diffusion/generator-heterozygosity.md) with eigenvalue $-1$, and the factors $e^{-\tau_e}$ multiply along the path by the Markov property), so the denominator equals $e^{-\tau}/2$, and the numerator
is bounded by it, since $|(c - a)(c - b)| \le 1$. **Claim** (Patterson et al. 2012, Appendix C, Theorem 1, case 3): $F_3^{\mathrm{het}}(C; A, B) \ge 0$, and likewise for a heterozygote
ascertained in $C$. The source proves it by reducing it to sign conditions such as $\mathbb E_0[(r - x)(x - a)\, a(1 - a)] \ge 0$ on the trees of its Figure C1. It evaluates them in
closed form from Kimura's eigenfunction expansion with computer algebra, for example $120\,T = v\,u(1 - u)(1 - v)(1 + v)(2u^3 + 4u^2 + 6u + 3)$ with $u = e^{-\tau_1}$ and $v = e^{-\tau_2}$.

## Depends on

- [Kimura's series is the density of the neutral Wright–Fisher transition kernel](../../population-genetics/diffusion-theory/wright-fisher-diffusion/identification-of-the-kimura-series-with-the-neu.md)

## Proof depends on

- [Decay of heterozygosity](../../population-genetics/diffusion-theory/wright-fisher-diffusion/generator-heterozygosity.md)
- [Convergence and PDEs of the neutral Gegenbauer series](../../population-genetics/diffusion-theory/wright-fisher-diffusion/kimura-1955-eigen-series-convergence-and-pde-for.md)

## Related topics

- [Ascertainment in an outgroup keeps f3 of an unadmixed target nonnegative](outgroup-ascertained-f3-positivity-patterson-app.md)

## Expansion

The closed forms of the source's three integrals (Figure C1A with ascertainment in $A$, and Figure C1B with ascertainment in $A$ and in $C$), and the
positivity of their polynomial factors, must be reproduced from the Kimura expansion; the source reports them from a computer-algebra calculation
that it does not print. This page records the statement and the reduction, not that calculation.

## Sources

- N. Patterson et al., "Ancient admixture in human history", Genetics 192 (2012), 1065–1093, <https://doi.org/10.1534/genetics.112.145037>, Appendix C, Theorems 1 and 2 and equations (A1)–(A3).
