# Adding a prophecy variable

Let $S = (\Sigma, F, N, L)$ be a [specification in the sense of Abadi and Lamport](../../refinement/refinement-mappings-prove-implementation.md). A specification $S^p = (\Sigma^p, F^p, N^p, L^p)$ is obtained from $S$ by *adding a prophecy variable* if, writing $\Pi_P$ for the projection from $\Sigma \times P$ onto $\Sigma$:

1. $\Sigma^p \subseteq \Sigma \times P$ for some set $P$;
2. $\Pi_P(F^p) \subseteq F$, and for every $(s, p) \in \Sigma^p$ with $s \in F$ there are $p_0, \dots, p_n = p$ with $(s, p_0) \in F^p$ and $\langle (s, p_i), (s, p_{i+1}) \rangle \in N^p$ for $0 \le i < n$;
3. if $\langle (s, p), (s', p') \rangle \in N^p$ then $\langle s, s' \rangle \in N$ or $s = s'$;
4. if $\langle s, s' \rangle \in N$ and $(s', p') \in \Sigma^p$, then there are $p, p'_0, \dots, p'_n = p'$ with $\langle (s, p), (s', p'_0) \rangle \in N^p$ and $\langle (s', p'_i), (s', p'_{i+1}) \rangle \in N^p$ for $0 \le i < n$;
5. $L^p$ consists of the behaviors whose projection under $\Pi_P$ is in $L$;
6. for every $s \in \Sigma$ the set of $p$ with $(s, p) \in \Sigma^p$ is finite and nonempty.

Condition 4 is the time reversal of the corresponding condition for history variables: every backward step of $S$ can be simulated, followed by steps that simulate stuttering. Condition 6 has no counterpart for history variables; it is needed because every behavior has an initial state but only terminating behaviors have a final one. A prophecy variable may thus predict future choices and add stuttering steps.

## Depends on

- [Refinement mappings prove implementation](../../refinement/refinement-mappings-prove-implementation.md)

## Sources

- M. Abadi and L. Lamport, "The existence of refinement mappings", *Theoretical Computer Science* 82(2):253–284, 1991, <https://doi.org/10.1016/0304-3975(91)90224-P>; the numbered locators refer to the research report version, SRC Research Report 29, Digital Equipment Corporation, 1988, <https://lamport.azurewebsites.net/pubs/abadi-existence.pdf>, Section 5.2 (conditions P1, P3, P5 and P6) and Section 5.3 (conditions P2 and P4, which allow stuttering).
