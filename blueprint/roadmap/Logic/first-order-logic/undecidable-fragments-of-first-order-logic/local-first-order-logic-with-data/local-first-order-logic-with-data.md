# Local first-order logic with data

Local first-order logic over data structures restricts quantification to the r-view of an element, the part of the structure reachable within distance r through shared data values, in order to regain decidability of satisfiability for first-order logic with data.

**Definition.** For a finite set $\Sigma$ of unary predicates and $Da \ge 0$, a *$Da$-data structure* $\mathfrak A = (A, (P_\sigma)_{\sigma \in \Sigma}, f_1, \ldots, f_{Da})$ has a nonempty **finite** set $A$, sets $P_\sigma \subseteq A$ and maps $f_i : A \to \mathbb N$ (the data values of each node). Each pair $(i, j)$ gives the relation $a \mathrel{{}_i{\sim}_j} b$ iff $f_i(a) = f_j(b)$. For a set $\Gamma$ of such symbols, $\mathrm{dFO}[Da, \Sigma, \Gamma]$ is first-order logic with atoms $\sigma(x)$, $x \mathrel{{}_i{\sim}_j} y$ for ${}_i{\sim}_j \in \Gamma$, and $x = y$.

The *data graph* $G(\mathfrak A)$ has vertices $A \times \{1, \ldots, Da\}$ and edges from $(a, i)$ to $(a, j)$ for $i \neq j$, and from $(a, i)$ to $(b, j)$ when ${}_i{\sim}_j \in \Gamma$ and $a \mathrel{{}_i{\sim}_j} b$. The *radius-$r$ ball* of $a$ is the set of vertices reachable from some $(a, i)$ by a directed path of length at most $r$, and the *$r$-view* $\mathfrak A|^r_a$ is the substructure on the nodes having a vertex in the ball, in which the data values of vertices outside the ball are replaced by pairwise distinct fresh values. The logic $r$-$\mathrm{Loc}$-$\mathrm{dFO}[Da, \Sigma, \Gamma]$ is

$$
\varphi ::= \langle\!\langle \psi \rangle\!\rangle^r_x \mid x = y \mid \exists x.\varphi \mid \varphi \vee \varphi \mid \neg\varphi,
$$

where $\psi$ is a $\mathrm{dFO}[Da, \Sigma, \Gamma]$ formula with at most the free variable $x$, and $\mathfrak A \models_I \langle\!\langle\psi\rangle\!\rangle^r_x$ iff $\mathfrak A|^r_{I(x)} \models_I \psi$. Its *existential fragment* $\exists$-$r$-$\mathrm{Loc}$-$\mathrm{dFO}$ allows only $\langle\!\langle\psi\rangle\!\rangle^r_x$, $x = y$, $x \neq y$, $\exists$, $\vee$ and $\wedge$ outside the local modalities (with $\psi$ unrestricted). $\mathrm{DataSat}(F, Da, \Gamma)$ asks, given $\Sigma$ and a sentence of $F[Da, \Sigma, \Gamma]$, whether some $Da$-data structure over $\Sigma$ satisfies it.

## Depends on

None.

## Proof depends on

None.

## Expansion

Full first-order logic over $2$-data structures with $\{{}_1{\sim}_1, {}_2{\sim}_2\}$ is already undecidable, since it can express two equivalence relations (Janiczak), even with $\Sigma = \emptyset$ (Theorem 2.2 of the source); with one data value it is N2EXP-complete. The local logics are decidable in several cases: $\mathrm{DataSat}(1\text{-}\mathrm{Loc}\text{-}\mathrm{dFO}, 2, \{{}_1{\sim}_1, {}_2{\sim}_2, {}_1{\sim}_2\})$ (Theorem 3.20), the existential fragment with radius $2$ and two data values (N2EXP-complete, Theorem 4.7), and the existential fragment with radius $1$ and any number of data values (NEXP-complete, Theorem 4.10). With radius $3$ and two data values, or radius $2$ and three, the existential fragment is undecidable ([radius 3, two data values](existential-local-fo-of-radius-3-with-two-data.md), [radius 2, three data values](existential-local-fo-of-radius-2-with-three-data.md); Theorems 4.13 and 4.15 of the source).

## Sources

- B. Bollig, A. Sangnier and O. Stietel, "On the Satisfiability of Local First-Order Logics with Data", *Logical Methods in Computer Science* 20(3), 2024, paper 1, pp. 1:1–1:42, <https://doi.org/10.46298/lmcs-20(3:1)2024>; numbers from arXiv:2307.00831v4, <https://arxiv.org/abs/2307.00831v4>: Section 2 (data structures, dFO, DataSat, Theorem 2.2, data graphs, views, local logics), Section 3 (Theorem 3.20) and Section 4 (the existential fragment, Theorems 4.7 and 4.10).
- A. Janiczak, "Undecidability of some simple formalized theories", *Fundamenta Mathematicae* 40:131–139, 1953, <https://doi.org/10.4064/fm-40-1-131-139>: undecidability of first-order logic with two equivalence relations, as recalled in Section 2 of the version of the first source read.
