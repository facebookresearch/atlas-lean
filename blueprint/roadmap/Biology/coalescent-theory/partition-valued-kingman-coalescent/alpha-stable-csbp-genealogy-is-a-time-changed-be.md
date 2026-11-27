# The genealogy of α-stable branching is a time-changed Beta-coalescent

This page covers a research programme around the theorem of Birkner, Blath, Capaldo, Etheridge, Möhle, Schweinsberg and Wakolbinger.

Let $Z$ be a continuous-state branching process with branching mechanism $\psi$, Gaussian coefficient $\sigma$ and Lévy measure $\nu$, and let $M$ be the associated measure-valued branching process, started from positive mass. Before the extinction or explosion time $\tau$, consider the ratio process $R_t = M_t / Z_t$, run on the inverse of an additive clock. The programme is to show:

- $R$ is a Markov process, of Λ-Fleming–Viot type, if and only if either $\nu = 0$ (the diffusion case, giving Kingman's coalescent and the Fleming–Viot process), or $\sigma = 0$ and $\nu$ is $\alpha$-stable with $\alpha \in (0, 2)$;
- in the second case with $1 < \alpha < 2$ the genealogy is the [Beta$(2 - \alpha, \alpha)$-coalescent](../multiple-merger-coalescents/merger-rates-and-beta-coalescents/beta-2-alpha-alpha-coalescent-n-sample-chains-pa.md).

The source warns that for $\alpha < 2$, $R$ is not a time change of a Fleming–Viot process independent of $Z$. No conditional independence or disintegration claim is made.

## Expansion

Split the programme into separately stated results, each with hypotheses fixed from the source: the normalization of $\psi$, the initial positive mass, sampling times before $\tau$, and the inverse additive clock with its constant. The forward direction is restricted to $1 < \alpha < 2$. The converse is stated with both alternatives.

Prerequisites:

- [The Beta-coalescent on a finite sample](../multiple-merger-coalescents/merger-rates-and-beta-coalescents/beta-2-alpha-alpha-coalescent-n-sample-chains-pa.md)

## Sources

- M. Birkner, J. Blath, M. Capaldo, A. Etheridge, M. Möhle, J. Schweinsberg and A. Wakolbinger, Alpha-stable branching and beta-coalescents, *Electron. J. Probab.* 10 (2005), 303–325, <https://doi.org/10.1214/EJP.v10-241> (main theorem).
