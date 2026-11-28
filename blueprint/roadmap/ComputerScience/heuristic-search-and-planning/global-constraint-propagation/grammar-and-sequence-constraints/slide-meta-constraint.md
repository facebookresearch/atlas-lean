# The SLIDE meta-constraint

SLIDE applies one constraint of arity $k$ to every window of $k$ consecutive variables of a sequence. If the slid constraint is monotone, propagating the windows separately already achieves generalized arc consistency, and for fixed $k\ge2$ a tree-shaped intersection encoding achieves it in $O(nd^k)$ time.

Let $C$ be a constraint of arity $k\ge1$ and $X_1,\dots,X_n$ distinct variables, $n\ge k$, with finite domains of size at most $d$. $\mathrm{SLIDE}(C,[X_1,\dots,X_n])$ holds iff $C(X_i,\dots,X_{i+k-1})$ holds for every $1\le i\le n-k+1$; more generally, for a stride $j\ge1$, $\mathrm{SLIDE}_j(C,[X_1,\dots,X_n])$ holds iff $C(X_{ij+1},\dots,X_{ij+k})$ holds for $0\le i\le\lfloor(n-k)/j\rfloor$, and $\mathrm{SLIDE}_1=\mathrm{SLIDE}$. When $j>k$ some variables lie in no window and are unconstrained apart from their domains. A constraint is **monotone** when some total order $\prec$ of the values makes every value $v$ substitutable for every $w\succ v$ in any support.

*The intersection encoding* (for $k\ge2$ and stride 1) has a variable $V_j$ for each block $X_j,\dots,X_{j+k-2}$ of $k-1$ consecutive variables, $1\le j\le n-k+2$, with domain $D(X_j)\times\dots\times D(X_{j+k-2})$; a binary compatibility constraint between $V_j$ and $V_{j+1}$ requires the two tuples to agree on their $k-2$ shared variables and their union to satisfy $C$; and one binary channelling constraint links each $X_i$ to one block containing it.

**Theorem.**

1. Suppose $C$ is monotone and every domain is nonempty. Then, if each window constraint $C(X_{ij+1},\dots,X_{ij+k})$ of the decomposition is [generalized arc consistent](../generalized-arc-consistency.md), so is $\mathrm{SLIDE}_j(C,[X_1,\dots,X_n])$.
2. Let $k\ge2$ be fixed and suppose that whether a $k$-tuple satisfies $C$ is decided in constant time. Enforcing arc consistency on the intersection encoding (reporting failure if a domain empties) achieves GAC on $\mathrm{SLIDE}(C,[X_1,\dots,X_n])$, in $O(nd^k)$ time and $O(nd^{k-1})$ space.

## Depends on

- [Generalized arc consistency](../generalized-arc-consistency.md): the consistency enforced.

## Proof depends on

- [Greedy assignment on a tree CSP](../../tree-csps-directional-arc-consistency-makes-gree/greedy-ne-none-iff.md): on a binary constraint network whose arcs form a forest, consistent arcs let a greedy root-first assignment extend any value of the root, after rerooting at the variable to be supported; used for item 2.

## Expansion

*Item 1.* To support $X=v$, give every other variable the $\prec$-least value of its domain (nonempty by assumption). Each window constraint is GAC, so it has a support for each of its values, and least values can replace the values of that support; hence the constructed tuple satisfies every window. With an empty domain the monotone argument has nothing to choose, and propagation reports failure instead.

*Item 2.* The constraint graph of the intersection encoding is a tree: a path $V_1,\dots,V_{n-k+2}$ of block variables with each original variable hanging off one block. On a tree-structured binary network arc consistency makes every value extendable to a solution: rerooting the tree at the variable of the value, the arcs from parents to children are consistent, and the greedy root-first assignment succeeds. Solutions of the encoding project onto the solutions of SLIDE, and the channelling constraints carry the pruning back to the $X_i$. There are $O(n)$ block variables with $O(d^{k-1})$ tuples each; arc consistency on one compatibility constraint takes $O(d^k)$ because each tuple of $V_j$ has at most $d$ partners in $V_{j+1}$, and each channelling constraint takes $O(d^{k-1})$ as it is functional. With $k=1$ the blocks would be empty and the encoding degenerates; a unary slid constraint simply filters each domain.

*On the omitted hardness clause.* The source also states that enforcing GAC on SLIDE is NP-hard when the arity of $C$ is not fixed, even if GAC on $C$ itself is polynomial; that claim is not part of this page. The source's proof sketch of its Theorem 2 reduces 3SAT with $N$ variables to a SLIDE of a constraint of arity $N+1$ over blocks of $N+1$ variables (one literal choice and a copy of the truth assignment per clause). Its definition of the slid constraint refers to $Y_{i+N+1}$ to pass the truth assignment from one block to the next, which lies outside a scope of arity $N+1$, so the synchronisation between blocks is not established as written. The hardness claim is therefore not stated on this page.

The source encodes AMONG sequences, REGULAR, STRETCH, LEX, ELEMENT and CARDPATH with SLIDE; for REGULAR the windows overlap in one variable, the decomposition is Berge-acyclic, and the plain decomposition already achieves GAC.

## Sources

- C. Bessiere, E. Hebrard, B. Hnich, Z. Kiziltan and Toby Walsh, "SLIDE: a useful special case of the CARDPATH constraint", *Proceedings of the 18th European Conference on Artificial Intelligence (ECAI 2008)*, Frontiers in Artificial Intelligence and Applications, IOS Press (2008), from p. 475, doi:10.3233/978-1-58603-891-5-475. Definitions of SLIDE, $\mathrm{SLIDE}_j$ and monotone constraints in §2, the intersection encoding and Theorems 1 and 3 with proofs (and Theorem 2 with its sketch) in §6 (Propagating SLIDE) of arXiv:0903.0471v1, [https://arxiv.org/abs/0903.0471v1](https://arxiv.org/abs/0903.0471v1).
