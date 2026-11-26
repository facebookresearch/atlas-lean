# Simplification ordering

The *proper subterm ordering* $\rhd$ on $T_\Sigma(X)$ is defined by $s \rhd t$ if $s|_p = t$ for some position $p \neq \varepsilon$ of $s$. A [rewrite ordering](reduction-ordering.md) $\succ$ on $T_\Sigma(X)$ is a *simplification ordering* if it has the *subterm property*: $s \rhd t$ implies $s \succ t$.

The *homeomorphic embedding* relations are defined from the [term rewriting system](../automated-deduction/term-rewriting-systems.md) $R_{\mathrm{emb}} = \{f(x_1, \dots, x_n) \to x_i \mid f \in \Sigma \text{ of arity } n,\ 1 \le i \le n\}$ by $\rhd_{\mathrm{emb}} = \to_{R_{\mathrm{emb}}}^+$ and $\unrhd_{\mathrm{emb}} = \to_{R_{\mathrm{emb}}}^*$; $\rhd_{\mathrm{emb}}$ is itself a simplification ordering.

## Depends on

- [Reduction ordering](reduction-ordering.md)
- [Abstract reduction system](abstract-reduction-system.md)
- [Term rewriting systems](../automated-deduction/term-rewriting-systems.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.5, simplification orderings and the homeomorphic embedding, p. 118.
