# Interference in strict SSA programs

Let $P$ be a program in [SSA form](../intermediate-representations/dominance-and-static-single-assignment-form.md), given as a control-flow graph of labels with a start label, in which every variable $v$ has a unique defining label $D_v$. The program is *strict* if every use of a variable $v$ is dominated by $D_v$. A variable is *live* at a label $\ell$ if some path from $\ell$ reaches a use of it without passing through its definition, in the sense of [live-variables analysis](../static-analysis/live-variables-analysis.md). Two variables *interfere* if some label exists at which both are live, and the *interference graph* has the variables as nodes and the interfering pairs as edges.

## Depends on

- [Dominance and static single assignment form](../intermediate-representations/dominance-and-static-single-assignment-form.md)
- [Live-variables analysis](../static-analysis/live-variables-analysis.md)

## Sources

- S. Hack, D. Grund and G. Goos, "Register allocation for programs in SSA-form", *Compiler Construction (CC 2006)*, LNCS 3923, Springer, 2006, pp. 247–262, <https://compilers.cs.uni-saarland.de/papers/ssara.pdf>, Section 2: Definitions 1–3 (dominance, strict programs and interference) and the notion of liveness used there.
