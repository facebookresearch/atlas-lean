# Congruence of the operational and denotational semantics of CSP

For a closed CSP term $P$ let $\Phi_T(P) = \mathrm{traces}(P)$, $\Phi_F(P) = (\mathrm{traces}(P), \mathrm{failures}(P))$ and $\Phi_N(P) = (\mathrm{failures}_\bot(P), \mathrm{divergences}(P))$, computed in the [operational semantics of CSP](csp-operational-semantics.md) by the [extraction of traces, failures and divergences](traces-failures-and-divergences-of-a-process.md). Then for every CSP term $P$ and every substitution $\xi$ of closed terms for its free process identifiers,

$$\Phi_T(\mathrm{subst}(P, \xi)) = S_T[\![P]\!]\xi^T \quad\text{and}\quad \Phi_F(\mathrm{subst}(P, \xi)) = S_F[\![P]\!]\xi^F,$$

where $\xi^T$ and $\xi^F$ are the environments obtained by applying $\Phi_T$ and $\Phi_F$ to each component of $\xi$, and $S_T$, $S_F$ are the [denotational semantics](denotational-semantics-of-csp.md) over the [traces](the-traces-model.md) and [stable failures](the-stable-failures-model.md) models. The same equation holds for $\Phi_N$ and $S_N$ over the [failures-divergences model](the-failures-divergences-model.md) whenever the instantiated term $\mathrm{subst}(P, \xi)$ is finitely nondeterministic, that is, involves no hiding of an infinite set, no infinite-to-one renaming and no nondeterministic choice over an infinite set. In particular, for every closed term the operational and denotational semantics give the same value in the traces and stable failures models, and for every finitely nondeterministic closed term also in the failures-divergences model.

## Depends on

- [The operational semantics of CSP](csp-operational-semantics.md)
- [Traces, failures and divergences of a process](traces-failures-and-divergences-of-a-process.md)
- [Denotational semantics of CSP](denotational-semantics-of-csp.md)
- [The traces model of CSP](the-traces-model.md)
- [The stable failures model of CSP](the-stable-failures-model.md)
- [The failures-divergences model of CSP](the-failures-divergences-model.md)

## Proof depends on

- [Kőnig's lemma for inverse systems](konig-s-lemma-for-inverse-systems.md)

## Sources

- A. W. Roscoe, *The Theory and Practice of Concurrency*, Prentice Hall, 1997; revised edition 2005, author's online version, <https://www.cs.ox.ac.uk/bill.roscoe/publications/68b.pdf>, Section 9.4 ("Relations with operational semantics"): the abstraction functions $\Phi_T$, $\Phi_F$, $\Phi_N$, the statement of the congruence result for all $\xi$ and all terms, its proof for $\mathcal{T}$ by structural induction with the recursion case, and the remarks extending it to $\mathcal{F}$ and, for finitely nondeterministic CSP using König's lemma, to $\mathcal{N}$; Section 8.3.2, which defines finitely nondeterministic CSP as the processes involving no infinite hiding, infinite-to-one renaming or infinite nondeterministic choice.
