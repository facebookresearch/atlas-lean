# Dependency pair chains

Let $R$ be a term rewriting system with [dependency pairs](dependency-pairs.md). A finite or infinite sequence of dependency pairs $\langle s_1, t_1\rangle \langle s_2, t_2\rangle \cdots$, with different occurrences renamed apart, is an *$R$-chain* if there is a substitution $\sigma$ with $t_j\sigma \to_R^* s_{j+1}\sigma$ for every two consecutive pairs. The *dependency graph* of $R$ has the dependency pairs as nodes and an arc from $\langle s, t\rangle$ to $\langle v, w\rangle$ if $\langle s, t\rangle\langle v, w\rangle$ is an $R$-chain. Every chain is a path in the dependency graph, but not conversely, since a path may use a different substitution for each arc.

## Depends on

- [Dependency pairs](dependency-pairs.md)

## Sources

- T. Arts and J. Giesl, "Termination of term rewriting using dependency pairs", *Theoretical Computer Science* 236(1–2):133–178, 2000, <https://verify.rwth-aachen.de/giesl/papers/TCS-distribute.pdf>, Section 2.1, Definition 5 (chains) and the conventions after it; Section 2.4, Definition 15 (dependency graph) and the remarks after it.
