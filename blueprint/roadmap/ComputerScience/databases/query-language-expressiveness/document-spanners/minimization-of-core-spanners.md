# Minimization of core spanner representations is not computable

For every reasonable size measure on core spanner representations, no algorithm transforms a representation into an equivalent one of minimal size.

A complexity measure for a class $\mathcal{S}$ of spanner representations is a total computable function $c \colon \mathcal{S} \to \mathbb{N}$ such that, for each alphabet, the representations of spanners over it can be effectively enumerated in order of increasing $c$, and only finitely many representations share any value of $c$. A representation $\hat\rho$ is $c$-minimal if no representation equivalent to it has a smaller value of $c$.

**Theorem.** Let $c$ be a complexity measure for the [core spanner representations](core-spanners.md) $\mathrm{RGX}^{\{\pi, \zeta^{=}, \cup, \bowtie\}}$ over a fixed alphabet with at least two letters. There is no algorithm that, given $\rho \in \mathrm{RGX}^{\{\pi, \zeta^{=}, \cup, \bowtie\}}$, computes an equivalent $\hat\rho \in \mathrm{RGX}^{\{\pi, \zeta^{=}, \cup, \bowtie\}}$ that is $c$-minimal.

## Depends on

- [Core spanners](core-spanners.md)

## Proof depends on

- [Universality and equivalence of core spanners are not semi-decidable](universality-of-core-spanners.md)

## Expansion

The set $U_{\min}$ of $c$-minimal representations of the universal Boolean spanner $\Upsilon_\emptyset$ is finite, by the definition of a complexity measure, so membership in it is decidable. A minimization algorithm would then decide whether $[\![\rho]\!] = \Upsilon_\emptyset$ by testing whether its output lies in $U_{\min}$, contradicting the undecidability of universality for Boolean core spanners.

## Sources

- Dominik D. Freydenberger and Mario Holldack, "Document spanners: from expressive power to decision problems", *Theory of Computing Systems* 62(4), 854–898, 2018, <https://doi.org/10.1007/s00224-017-9770-0>; read as the open-access publisher version, <https://link.springer.com/content/pdf/10.1007/s00224-017-9770-0.pdf>: Definition 4.8 (complexity measures, after Kutrib) and Theorem 4.9 with its proof.
