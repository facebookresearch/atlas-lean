# Attractors via forward and backward reachability

Let a gene regulatory network on $N$ genes be given by Boolean update functions $f_1, \dots, f_N : \{0,1\}^N \to \{0,1\}$. The **synchronous** transition relation updates all genes at once, $x \to f(x) = (f_1(x), \dots, f_N(x))$, so every state has exactly one successor; the **asynchronous** relation updates one gene at a time, $x \to (x_1, \dots, f_i(x), \dots, x_N)$ for each $i$ with $f_i(x) \ne x_i$ (and $x \to x$ if there is no such $i$). Either relation defines a state transition graph $T$ on the $2^N$ states. For a set of states $S_0$, let $FR(S_0)$ be the set of states reachable from $S_0$ by directed paths of length $\ge 0$ (iterated forward images), and $BR(S_0)$ the set of states from which $S_0$ is reachable (iterated backward images). An **attractor** is a nonempty set $A$ with $FR(s) = A$ for every $s \in A$; a **steady state** is a one-element attractor.

**Theorem.** In any finite state transition graph:
1. a state $i$ belongs to an attractor if and only if $FR(i) \subseteq BR(i)$; otherwise $i$ is transient;
2. if $i$ is transient, every state of $BR(i)$ is transient;
3. if $i$ belongs to an attractor, that attractor is $FR(i)$, and every state of $BR(i) \setminus FR(i)$ is transient.

Consequently the attractors are exactly the terminal strongly connected components of $T$, and they can be enumerated by repeatedly picking a seed state, computing $FR$ and $BR$, recording $FR$ as an attractor when item 1 holds, and deleting $BR$ from the remaining state space. Under the synchronous relation every attractor is a single directed cycle (a steady state or a limit cycle); the steady states (fixed points $f(x) = x$) are the same for the synchronous and asynchronous relations, while cyclic attractors generally differ.

## Expansion

If $FR(i) \subseteq BR(i)$, every $j \in FR(i)$ can return to $i$, so $FR(j) = FR(i)$ and $FR(i)$ is an attractor containing $i$; conversely, if $i$ lies in an attractor $A$ then $FR(i) = A$ and every state of $A$ reaches $i$. If $i$ is transient then some state reachable from $i$ cannot return; any $k$ reaching $i$ also reaches that state, so $k$ is transient. Since $FR(i)$ is closed under successors and strongly connected, it is a terminal strongly connected component, and every state that reaches it without being in it is transient. Representing state sets and the transition relation as reduced ordered binary decision diagrams makes the image computations symbolic, which handles networks far beyond explicit enumeration of $2^N$ states; fixed points coincide across semantics because $f(x) = x$ is exactly the condition that no gene can change. A combined strategy finds candidate attractors synchronously and then verifies them asynchronously.

## Sources

- A. Garg, A. Di Cara, I. Xenarios, L. Mendoza, G. De Micheli, "Synchronous versus asynchronous modeling of gene regulatory networks", Bioinformatics 24(17) (2008) 1917–1925, Eqs. (3)–(4), Definitions 1–6, Theorems 1–2 (after Xie and Beerel) and Algorithms 2–3, <https://doi.org/10.1093/bioinformatics/btn336>, PMCID PMC2519162.
