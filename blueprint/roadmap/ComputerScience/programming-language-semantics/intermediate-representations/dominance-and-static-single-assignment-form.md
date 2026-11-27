# Dominance and static single assignment form

Let $G$ be a control-flow graph of basic blocks with an entry block from which every block is reachable.

- **Dominance.** A block $n_1$ *dominates* $n_2$ if every path in $G$ from the entry to $n_2$ includes $n_1$. Every block dominates itself, and $n_1$ *strictly dominates* $n_2$ if it dominates $n_2$ and $n_1 \ne n_2$. Every block other than the entry has a unique immediate dominator: a strict dominator that does not dominate any other strict dominator of it. The dominance relation forms a tree rooted at the entry.
- **SSA form.** A program is in *static single assignment* (SSA) form if every variable has exactly one static definition. At the head of a block with predecessors $B_1, \dots, B_n$, a $\varphi$-function $a_0 = \varphi(B_1 : a_1, \dots, B_n : a_n)$ takes the value $a_i$ when control arrives from $B_i$. All $\varphi$-functions at the head of a block execute in parallel, that is, simultaneously and not sequentially. This matters when the target of one $\varphi$-function is a source of another.
- **Strictness.** A procedure is *strict* if every variable is defined before it is used along every path from the entry. In SSA form strictness is equivalent to the *dominance property*: each use of a variable is dominated by its definition.
- **Pruned and minimal form.** An SSA program is *pruned* if every $\varphi$-function has, transitively, at least one user that is not a $\varphi$-function. A $\varphi$-function for $v$ in block $Z$ is *necessary* if two nonempty paths from blocks $X$ and $Y$ containing assignments to $v$ converge first at $Z$. A program whose $\varphi$-functions are all necessary is in *minimal* SSA form.

## Sources

- F. Rastello and F. Bouchez Tichadou (eds.), *SSA-based Compiler Design*, Springer, 2022; public draft of 8 June 2018, <https://pfalcon.github.io/ssabook/latest/book-full.pdf>, Section 1.2 (informal semantics of SSA, parallel execution of $\varphi$-functions) and Section 2.3 (strict SSA form and the dominance property).
- M. Braun, S. Buchwald, S. Hack, R. Leißa, C. Mallon and A. Zwinkau, "Simple and efficient construction of static single assignment form", *Compiler Construction (CC 2013)*, LNCS 7791, Springer, 2013, Section 4: pruned SSA form, Definitions 1 and 2 (path convergence and necessary $\varphi$-functions, after Cytron et al.), and the definitions of dominance and immediate dominance.
- R. Cytron, J. Ferrante, B. K. Rosen, M. N. Wegman and F. K. Zadeck, "Efficiently computing static single assignment form and the control dependence graph", *ACM Transactions on Programming Languages and Systems* 13(4):451–490, 1991.
