# Termination criterion via dependency pairs

A term rewriting system $R$ terminates if and only if there is no infinite [$R$-chain](dependency-pair-chains.md) of dependency pairs.

**Proof idea.** From an infinite reduction take a minimal subterm $f(\vec u)$ starting one, whose arguments are strongly normalizing. Eventually a rule $f(\vec w) \to r$ is applied at the root, and $r\sigma$ contains a subterm $g(\vec u')$ with defined root that starts an infinite reduction and has strongly normalizing arguments; since the values of $\sigma$ are strongly normalizing, this subterm is an instance of a subterm $g(\vec t)$ of $r$ itself, so $\langle F(\vec w), G(\vec t)\rangle$ is a dependency pair. This gives a dependency pair, and repeating gives an infinite chain. Conversely an infinite chain yields an infinite reduction, as tuple symbols are not defined.

## Depends on

- [Dependency pair chains](dependency-pair-chains.md)

## Sources

- T. Arts and J. Giesl, "Termination of term rewriting using dependency pairs", *Theoretical Computer Science* 236(1–2):133–178, 2000, <https://verify.rwth-aachen.de/giesl/papers/TCS-distribute.pdf>, Section 2.1, Theorem 6 (termination criterion) and its proof.
