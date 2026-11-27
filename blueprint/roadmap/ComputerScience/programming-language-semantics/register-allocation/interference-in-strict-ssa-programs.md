# Interference in strict SSA programs

Let $P$ be a program in [SSA form](../intermediate-representations/dominance-and-static-single-assignment-form.md), given as a control-flow graph of labels with a start label, in which every variable $v$ has a unique defining label $D_v$. The program is *strict* if every use of a variable $v$ is dominated by $D_v$. Every variable is used at least once. A variable $v$ is *live* at a label $\ell$ if some path from $D_v$ through $\ell$ to a use of $v$ does not return to $D_v$, as in [live-variables analysis](../static-analysis/live-variables-analysis.md) except that $v$ also counts as live at $D_v$. The operand of a $\varphi$-function for a predecessor $\ell'$ is used at the end of $\ell'$, and the $\varphi$-functions of a label define their results simultaneously at that label. Two variables *interfere* if some label exists at which both are live, and the *interference graph* has the variables as nodes and the interfering pairs as edges. Because a variable counts as live both at the label that defines it and at the labels that use it, this relation is coarser than the interference used for register assignment: it relates the operand $x$ and the result $y$ of $y \leftarrow x + 1$ even when $x$ is not used afterwards.

## Depends on

- [Dominance and static single assignment form](../intermediate-representations/dominance-and-static-single-assignment-form.md)
- [Live-variables analysis](../static-analysis/live-variables-analysis.md)

## Sources

- S. Hack, D. Grund and G. Goos, "Register allocation for programs in SSA-form", *Compiler Construction (CC 2006)*, LNCS 3923, Springer, 2006, pp. 247–262, <https://compilers.cs.uni-saarland.de/papers/ssara.pdf>, Section 2: Definitions 1–3 (dominance, strict programs and interference) and the notion of liveness used there, and Section 4 on $\varphi$-operations. The conventions that every variable is used, counts as live at its definition, and has its $\varphi$-operands used at the ends of the predecessors are written out here; without them a variable with no later use would form a clique with no label where it is live.
