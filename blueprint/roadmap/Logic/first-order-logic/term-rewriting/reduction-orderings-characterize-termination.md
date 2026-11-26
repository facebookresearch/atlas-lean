# Reduction orderings characterize termination

A [term rewriting system](../automated-deduction/term-rewriting-systems.md) $R$ is terminating if and only if there is a [reduction ordering](reduction-ordering.md) $\succ$ such that $l \succ r$ for every rule $l \to r$ of $R$.

**Proof.** If $l \succ r$ for all rules, then stability under substitutions and compatibility with contexts give $t[l\sigma]_p \succ t[r\sigma]_p$, so $\to_R\ \subseteq\ \succ$, and $\to_R$ terminates because $\succ$ is well-founded. Conversely, if $\to_R$ terminates, then $\succ\ = \to_R^+$ is a reduction ordering containing every rule.

## Depends on

- [Reduction ordering](reduction-ordering.md)
- [Abstract reduction system](abstract-reduction-system.md)
- [Term rewriting systems](../automated-deduction/term-rewriting-systems.md)

## Proof depends on

- [Termination via well-founded orderings](termination-via-well-founded-orderings.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.5, Theorem 4.19 with its proof, p. 115.
