# Translation to static single assignment form

A program is in *SSA form* if each variable is the target of exactly one assignment in the program text. A $\varphi$-function $V \leftarrow \varphi(R, S, \dots)$ at the head of a node with predecessors numbered $1, 2, \dots$ has one operand per predecessor and, when control enters from the $j$-th predecessor, takes the value of the $j$-th operand; the $\varphi$-functions of a node execute before its ordinary statements.

A *translation to SSA form* replaces a program by a program with the same control-flow graph such that, for every original variable $V$:

1. if two nonnull paths from nodes $X$ and $Y$ that contain assignments to $V$ [converge](../converging-paths-and-join-sets.md) at a node $Z$, then a trivial $\varphi$-function $V \leftarrow \varphi(V, \dots, V)$ has been inserted at $Z$;
2. each mention of $V$ in the original program or in an inserted $\varphi$-function has been replaced by a mention of a new variable $V_i$, leaving the new program in SSA form;
3. along any control-flow path, at any use of $V$ in the original program and the corresponding use of $V_i$ in the new program, $V$ and $V_i$ have the same value.

A translation is to *minimal SSA form* if it inserts as few $\varphi$-functions as possible subject to condition 1. The control-flow graph has an entry node with edges to the nodes where the program can be entered and no incoming edges, and the entry node is treated as containing an assignment to every variable. A conditional branch counts as an ordinary assignment to a special variable whose value selects the edge to follow, so mentions in branch expressions are renamed like other uses.

The *renaming* step visits the dominator tree top down, keeping for each variable $V$ a counter $C(V)$ and a stack $S(V)$ of indices. At each node it processes the statements in order, the $\varphi$-functions first: for an ordinary assignment it first replaces every use of $V$ by $V_i$ for $i$ the top of $S(V)$, and then, for every statement, it replaces the target $V$ by $V_i$ for $i = C(V)$, pushes $i$ and increments $C(V)$; the operands of $\varphi$-functions are not renamed here. The order matters: in a node $x \leftarrow 1;\ y \leftarrow x$, the use of $x$ must be renamed after the target of $x \leftarrow 1$. After the statements it fills the operand of each $\varphi$-function in each successor for the edge from this node with $V_i$ for $i$ the top of $S(V)$; recurses into the children; and finally pops what it pushed.

## Depends on

- [Converging paths and join sets](../converging-paths-and-join-sets.md)
- [Dominance and static single assignment form](../dominance-and-static-single-assignment-form.md)

## Sources

- R. Cytron, J. Ferrante, B. K. Rosen, M. N. Wegman and F. K. Zadeck, "Efficiently computing static single assignment form and the control dependence graph", *ACM Transactions on Programming Languages and Systems* 13(4):451–490, 1991, Section 2 (control-flow graph conventions), Section 3 (SSA form, the semantics of $\varphi$-functions, the three conditions on a translation and minimal SSA form) and Section 5.2 (Figure 12, the renaming algorithm).
