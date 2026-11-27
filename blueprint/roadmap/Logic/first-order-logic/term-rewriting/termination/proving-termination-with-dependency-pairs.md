# Proving termination with dependency pairs

A term rewriting system $R$ terminates if and only if there is a well-founded weakly monotonic quasi-ordering $\succsim$, with strict part $>$, both closed under substitution, such that $l \succsim r$ for every rule $l \to r$ of $R$ and $s > t$ for every [dependency pair](dependency-pairs.md) $\langle s, t\rangle$.

For a finite term rewriting system, it suffices to require $s \succsim t$ for the dependency pairs on each cycle of the [dependency graph](dependency-pair-chains.md), with $s > t$ for at least one dependency pair on each cycle. Finiteness is needed for this refinement: the infinitely many ground rules $f(s^n(0)) \to f(s^{n+1}(0))$ give an infinite reduction, while their dependency graph is an infinite path without cycles, so the cycle conditions hold vacuously.

**Proof idea.** Rewrite steps are contained in $\succsim$, so an infinite chain would give $s_1\sigma > t_1\sigma \succsim s_2\sigma > \cdots$, contradicting well-foundedness; the [criterion](termination-criterion-via-dependency-pairs.md) gives termination. For the refinement, an infinite chain traverses some cycle of the finite dependency graph infinitely often. The source proves necessity with the rewrite ordering of the augmented system $R \cup \{s \to t \mid \langle s, t\rangle \text{ a dependency pair of } R\}$, which terminates when $R$ does.

## Depends on

- [Dependency pairs](dependency-pairs.md)
- [Dependency pair chains](dependency-pair-chains.md)

## Proof depends on

- [Termination criterion via dependency pairs](termination-criterion-via-dependency-pairs.md)

## Sources

- T. Arts and J. Giesl, "Termination of term rewriting using dependency pairs", *Theoretical Computer Science* 236(1–2):133–178, 2000, <https://verify.rwth-aachen.de/giesl/papers/TCS-distribute.pdf>, Section 2.2, Theorem 7 (proving termination) and its proof; Section 2.4, Theorem 18 (dependency graph refinement) and its proof, which uses that there are only finitely many dependency pairs.
