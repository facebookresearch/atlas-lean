# Adding a history variable

Let $S = (\Sigma, F, N, L)$ be a [specification in the sense of Abadi and Lamport](../../refinement/refinement-mappings-prove-implementation.md), with state space $\Sigma \subseteq \Sigma_E \times \Sigma_I$, initial states $F$, next-state relation $N$ and supplementary property $L$. A specification $S^h = (\Sigma^h, F^h, N^h, L^h)$ is obtained from $S$ by *adding a history variable* if, writing $\Pi_H$ for the projection from $\Sigma \times H$ onto $\Sigma$:

1. $\Sigma^h \subseteq \Sigma \times H$ for some set $H$, with $(\Sigma_E \times \Sigma_I) \times H$ read as $\Sigma_E \times (\Sigma_I \times H)$;
2. $\Pi_H(F^h) = F$;
3. if $\langle (s, h), (s', h') \rangle \in N^h$ then $\langle s, s' \rangle \in N$ or $s = s'$;
4. if $\langle s, s' \rangle \in N$ and $(s, h) \in \Sigma^h$, then $\langle (s, h), (s', h') \rangle \in N^h$ for some $h' \in H$;
5. $L^h$ consists of the behaviors whose projection under $\Pi_H$ is in $L$.

The new component records past information without affecting the behavior of the original components.

## Depends on

- [Refinement mappings prove implementation](../../refinement/refinement-mappings-prove-implementation.md)

## Sources

- M. Abadi and L. Lamport, "The existence of refinement mappings", *Theoretical Computer Science* 82(2):253–284, 1991, <https://doi.org/10.1016/0304-3975(91)90224-P>; the numbered locators refer to the research report version, SRC Research Report 29, Digital Equipment Corporation, 1988, <https://lamport.azurewebsites.net/pubs/abadi-existence.pdf>, Section 5.1, conditions H1–H5.
