# Machine closure, finite invisible nondeterminism and internal continuity

Let $S = (\Sigma, F, N, L)$ be a [specification](../../refinement/refinement-mappings-prove-implementation.md) with machine property $M$, property $P = M \cap L$ and induced externally visible property $O$, and let $\overline{X}$ denote the closure of a set of behaviors $X$, the set of behaviors all of whose finite prefixes are prefixes of behaviors in $X$.

- $S$ is *machine closed* if $M = \overline{M \cap L}$: the supplementary property specifies no safety property beyond the state machine.
- A property $P$ is *finitely invisibly nondeterministic* (fin) if for every externally visible behavior $\sigma \in O$ and every $n \ge 0$, the prefix of $\sigma$ of length $n$ is the projection of only finitely many finite prefixes of behaviors in $P$, up to the removal of stuttering steps. $S$ is fin if its property $P$ is.
- A property $P$ is *internally continuous* if every behavior $\sigma$ whose externally visible projection lies in $O$ and which lies in $\overline{P}$ lies in $P$. $S$ is internally continuous if its property is.

Every safety property has a fin specification, every specification of a safety property is internally continuous, and every property has a machine-closed specification. For a fin state machine, the externally visible property it induces is a safety property.

## Depends on

- [Refinement mappings prove implementation](../../refinement/refinement-mappings-prove-implementation.md)

## Sources

- M. Abadi and L. Lamport, "The existence of refinement mappings", *Theoretical Computer Science* 82(2):253–284, 1991, <https://doi.org/10.1016/0304-3975(91)90224-P>; the numbered locators refer to the research report version, SRC Research Report 29, Digital Equipment Corporation, 1988, <https://lamport.azurewebsites.net/pubs/abadi-existence.pdf>, Section 2 (machine closure), Section 3 (Definition 1 and Proposition 2) and Section 6 (Definition 2); the introduction states the three facts about safety properties.
