# Register allocation after classical SSA elimination is NP-complete

*Classical SSA elimination* replaces each $\varphi$-function $v = \varphi(v_1, \dots, v_m)$ of a program in [SSA form](../intermediate-representations/dominance-and-static-single-assignment-form.md) by copy instructions $v = v_i$ at the end of the predecessor blocks. A *simple post-SSA program* is a program of the form produced in this way from an SSA program with a single loop: it copies its parameters into temporaries, contains one loop with copy instructions just before the loop and at its end corresponding to one eliminated matrix of $\varphi$-functions, and returns.

**Theorem.** The [core register allocation problem](register-allocation-is-np-complete.md), with the number $K$ of registers part of the input, is NP-complete for simple post-SSA programs.

The proof reduces the coloring problem for circular-arc graphs: a circular graph $V$ with $\min(V) > K$ is $K$-colorable if and only if an associated *SSA-circular* graph $F(V, K)$ is, and an SSA-circular graph $Y$ is $K$-colorable if and only if the core register allocation problem has a solution for an associated simple post-SSA program $H(Y, K)$ with $K + 1$ registers. The result holds whatever the order in which the copies are inserted. So, although register allocation is polynomial for [strict SSA programs](optimal-coloring-of-ssa-interference-graphs.md), translating to SSA form, allocating registers and then eliminating SSA classically does not give a polynomial algorithm unless P = NP.

## Depends on

- [Register allocation is NP-complete](register-allocation-is-np-complete.md)
- [Dominance and static single assignment form](../intermediate-representations/dominance-and-static-single-assignment-form.md)

## Sources

- F. M. Q. Pereira and J. Palsberg, "Register allocation after classical SSA elimination is NP-complete", *Foundations of Software Science and Computation Structures (FoSSaCS 2006)*, <https://web.cs.ucla.edu/~palsberg/paper/fossacs06.pdf>: the abstract; Section 1.1 (the core register allocation problem, SSA form and post-SSA programs, Figure 3 with the grammar of simple post-SSA programs); Section 2 (circular and SSA-circular graphs, Lemmas 1–4); Section 3 (Lemma 5 and Theorem 1); and the remark after Theorem 1 on the order of copy insertion.
