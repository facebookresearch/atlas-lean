# The earlier of two interfering SSA variables is live at the later definition

Let $P$ be a strict program in SSA form in which every variable $v$ has a unique defining label $D_v$, with the interference relation of [interference in strict SSA programs](interference-in-strict-ssa-programs.md). If $v$ and $w$ interfere and $D_v$ dominates $D_w$, then $v$ is live at $D_w$.

**Proof idea.** Let $\ell$ be a label where both are live. A variable live at $\ell$ has its definition dominating $\ell$, by strictness. Take an entry path to $\ell$ and its segment from the last occurrence of $D_w$ to $\ell$. If this segment passed through $D_v \ne D_w$, then an entry path to $D_v$ avoiding $D_w$, which exists because $D_w$ does not dominate $D_v$, followed by the rest of the segment would reach $\ell$ without $D_w$. So the segment avoids $D_v$. A path from $D_v$ to $D_w$, then this segment, then a path from $\ell$ to a use of $v$ that does not return to $D_v$ shows that $v$ is live at $D_w$.

## Depends on

- [Interference in strict SSA programs](interference-in-strict-ssa-programs.md)

## Sources

- S. Hack, D. Grund and G. Goos, "Register allocation for programs in SSA-form", *Compiler Construction (CC 2006)*, LNCS 3923, Springer, 2006, pp. 247–262, <https://compilers.cs.uni-saarland.de/papers/ssara.pdf>, Section 2, Lemma 2, attributed there to Z. Budimlić et al., "Fast copy coalescing and live-range identification", PLDI 2002.
