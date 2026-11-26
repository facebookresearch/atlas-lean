# Infinite lookdown, de Finetti limit and the Λ-Fleming–Viot process

This page covers a research programme: the infinite modified lookdown construction for a Λ-coalescent, and the Λ-Fleming–Viot process it produces.

Fix a finite measure $\Lambda$ on $[0, 1]$ and a compact metric type space $E$, finite $E$ first. The programme is to show the following.

- The finite levels of the modified lookdown construction for the Λ-coalescent are consistent as the number of levels grows, so they define one infinite system of levels. Only the Kingman case of the finite-level statement is [the finite-level lookdown chain](finite-level-lookdown-chain-and-its-embedded-lam.md).
- At each fixed time the types of the levels are exchangeable, so by the [de Finetti theorem](../../../Probability/foundations/exchangeable-sequences/de-finetti-theorem-for-exchangeable-sequences-in.md) they have an empirical measure $X_t$.
- $t \mapsto X_t$ has càdlàg paths in the probability measures on $E$, and $X$ solves the Λ-Fleming–Viot martingale problem for the Λ polynomial operator. For two types this supplies a solution for the [conditional moment duality](conditional-lambda-wright-fisher-lambda-coalesce.md).
- The genealogy of the levels is the [Λ-coalescent on $\mathbb{N}$](../multiple-merger-coalescents/speed-of-coming-down-from-infinity/lambda-coalescent-on-n-as-a-time-indexed-cadlag.md).

The limits have jumps when $\Lambda \ne \Lambda(\{0\}) \delta_0$, so the continuity (C-tightness) argument of the Kingman case, [the finite-type lookdown directing process](../../population-genetics/diffusion-theory/fleming-viot-processes/lookdown-directing-process-is-the-finite-type-fl.md), is not reused without a version that allows jumps.

## Expansion

Split the programme into separately stated results, each with hypotheses fixed from a source:

1. Consistency of the infinite modified lookdown levels and exchangeability at fixed times.
2. Existence of the empirical measure process and its càdlàg modification. Càdlàg paths in the space of probability measures are a missing prerequisite. The [Poisson point process with finite intensity](../../../Probability/point-processes/poisson-point-processes/poisson-point-process.md) is not measure-valued path infrastructure.
3. The martingale problem satisfied by the limit.
4. The genealogy of the levels as the Λ-coalescent on $\mathbb{N}$.

Prerequisites:

- [The first n lookdown levels have Kingman's coalescent as genealogy](finite-level-lookdown-chain-and-its-embedded-lam.md)
- [Conditional moment duality between the Λ-Wright–Fisher process and the Λ-coalescent](conditional-lambda-wright-fisher-lambda-coalesce.md)
- [The Λ-coalescent on $\mathbb{N}$ as a càdlàg partition process](../multiple-merger-coalescents/speed-of-coming-down-from-infinity/lambda-coalescent-on-n-as-a-time-indexed-cadlag.md)
- [De Finetti theorem for exchangeable sequences](../../../Probability/foundations/exchangeable-sequences/de-finetti-theorem-for-exchangeable-sequences-in.md)
- [The finite-level lookdown process](../../population-genetics/diffusion-theory/fleming-viot-processes/finite-level-lookdown-process-and-projective-con.md)

## Sources

- P. Donnelly and T. G. Kurtz, Particle representations for measure-valued population models, *Ann. Probab.* 27 (1999), 166–205, <https://doi.org/10.1214/aop/1022677258> (particle representations).
- A. Etheridge, *Some Mathematical Models from Population Genetics*, École d'Été de Probabilités de Saint-Flour XXXIX-2009, Lecture Notes in Mathematics 2012 (2011), <https://link.springer.com/book/10.1007/978-3-642-16632-7> (lookdown).
