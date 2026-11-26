# Interfering variables of a strict SSA program are simultaneously live

Let $P$ be a program in [SSA form](../intermediate-representations/dominance-and-static-single-assignment-form.md), given as a control-flow graph of labels with a start label, in which every variable $v$ has a unique defining label $D_v$. Suppose $P$ is *strict*: every use of a variable $v$ is dominated by $D_v$. Here two variables *interfere* if some label exists at which both are live, and the interference graph has the variables as nodes and interfering pairs as edges.

1. If $v$ and $w$ interfere, then $D_v$ dominates $D_w$ or $D_w$ dominates $D_v$.
2. If $v$ and $w$ interfere and $D_v$ dominates $D_w$, then $v$ is live at $D_w$.
3. Consequently, for every clique $C$ of the interference graph there is a label at which all variables of $C$ are live.

**Proof of part 3.** By part 1 the defining labels of the variables of $C$ are totally ordered by dominance, so they can be listed as $D_{c_1}, \dots, D_{c_n}$ with each dominating the next. By part 2 every $c_i$ is live at $D_{c_n}$.

So the size of the largest clique equals the largest number of variables live at one label.

## Depends on

- [Dominance and static single assignment form](../intermediate-representations/dominance-and-static-single-assignment-form.md)
- [Live-variables analysis](../static-analysis/live-variables-analysis.md)

## Sources

- S. Hack, D. Grund and G. Goos, "Register allocation for programs in SSA-form", *Compiler Construction (CC 2006)*, LNCS 3923, Springer, 2006, pp. 247–262, <https://compilers.cs.uni-saarland.de/papers/ssara.pdf>, Section 2: Definitions 1–3 (dominance, strict programs, interference), Lemmas 1 and 2 (due to Budimlić) and Theorem 1 with its proof.
