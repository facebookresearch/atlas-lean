# Differential item functioning and group impact are logically independent

Put both groups on the same finite set of ability levels. For each group $g\in\{A,B\}$, let $\pi_g$ be its distribution of ability and $q_g(\theta)\in[0,1]$ its conditional probability of success on one binary item at ability $\theta$. Its [marginal success probability](item-success-marginal.md) is the [latent average](item-success-marginal-eq-sum.md) $m_g=\sum_\theta\pi_g(\theta)q_g(\theta)$. Differential item functioning (DIF) means that the two curves differ at some ability level. Group impact means that the two marginal probabilities differ.

If the two curves coincide with a common curve $q$, the [marginal difference under equal curves](../../not-yet-classified/part-16/impact-difference-of-equal-curves.md) is $m_A-m_B=\sum_\theta(\pi_A(\theta)-\pi_B(\theta))q(\theta)$. The following pairs on two ability levels show that neither difference implies the other:

- **Impact without DIF.** Both curves are $(1/4,3/4)$. The ability distributions $(3/4,1/4)$ and $(1/4,3/4)$ give marginals $3/8$ and $5/8$, respectively.
- **DIF without impact.** The curves are $(1/4,3/4)$ and $(1/2,1/2)$. Under the common ability distribution $(1/2,1/2)$, both marginals are $1/2$.

## Background

- [Affine rescaling of a finite 2PL latent mixture](../../not-yet-classified/part-06/finite-linking/finite-mixture-two-pl-affine-of-pos.md): a positive affine rescaling of one group's ability coordinate with the corresponding change in item parameters preserves that group's observed law. Comparing curves at the same ability level requires a common, anchored scale.

## Sources

- The identity and examples are derived here from the finite mixture formula.
