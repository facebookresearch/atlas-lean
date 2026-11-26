# Interfering SSA variables have comparable definitions

Let $P$ be a strict program in SSA form in which every variable $v$ has a unique defining label $D_v$, with the interference relation of [interference in strict SSA programs](interference-in-strict-ssa-programs.md). If $v$ and $w$ interfere, then $D_v$ dominates $D_w$ or $D_w$ dominates $D_v$.

**Proof idea.** At a label $\ell$ where both are live, both definitions dominate $\ell$ by strictness, and the dominators of a label are totally ordered by dominance.

## Depends on

- [Interference in strict SSA programs](interference-in-strict-ssa-programs.md)

## Sources

- S. Hack, D. Grund and G. Goos, "Register allocation for programs in SSA-form", *Compiler Construction (CC 2006)*, LNCS 3923, Springer, 2006, pp. 247–262, <https://compilers.cs.uni-saarland.de/papers/ssara.pdf>, Section 2, Lemma 1, attributed there to Z. Budimlić et al., "Fast copy coalescing and live-range identification", PLDI 2002.
