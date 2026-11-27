# Local first-order logic over data structures

A $D$-data structure is a finite set of nodes, each labeled by unary predicates and carrying $D$ natural-number data values; first-order logic compares data values by equality. Local first-order logic evaluates each subformula $\langle\psi\rangle^r_x$ only on the radius-$r$ view of $x$, and its existential fragment uses only existential quantifiers outside these local modalities.

**Data structures.** Fix a finite set $\Sigma$ of unary predicates and $D \geq 0$. A *$D$-data structure* over $\Sigma$ is $\mathfrak{A} = (A, (P_\sigma)_{\sigma \in \Sigma}, f_1, \dots, f_D)$ with $A$ a nonempty *finite* set, $P_\sigma \subseteq A$, and $f_i : A \to \mathbb{N}$; $f_i(a)$ is the $i$-th data value of node $a$. For $i, j \in \{1, \dots, D\}$, the relation $a \sim_{i,j} b$ means $f_i(a) = f_j(b)$. $\mathrm{Data}[\Sigma, D]$ is the set of these structures.

**First-order logic.** $\mathrm{dFO}[\Sigma, D]$ has formulas $\varphi ::= \sigma(x) \mid x \sim_{i,j} y \mid x = y \mid \varphi \vee \varphi \mid \neg\varphi \mid \exists x.\varphi$, with the usual semantics on $D$-data structures.

**Views and local logic.** The *data graph* of $\mathfrak{A}$ has vertices $A \times \{1, \dots, D\}$ and an edge between $(a, i)$ and $(b, j)$ iff $a = b$ or $a \sim_{i,j} b$. The *radius-$r$ ball* around $a$ is the set of vertices at distance at most $r$ from some $(a, i)$. The *$r$-view* of $a$ is the structure obtained from $\mathfrak{A}$ by replacing every data value $f_i(b)$ with $(b, i)$ outside this ball by a fresh value, distinct for each such pair. The *local modality* $\langle\psi\rangle^r_x$, for $\psi \in \mathrm{dFO}[\Sigma, D]$ with at most the free variable $x$, is true at $a$ exactly when $\psi(a)$ is true in the $r$-view of $a$. The *existential local fragment* $\exists$-$r$-$\mathrm{Loc}$-$\mathrm{dFO}[\Sigma, D]$ has formulas

$$
\varphi ::= \langle\psi\rangle^r_x \mid x = y \mid \neg(x = y) \mid \exists x.\varphi \mid \varphi \vee \varphi \mid \varphi \wedge \varphi,
$$

with no restriction on the quantifiers inside $\psi$.

**Satisfiability.** For a class $\mathcal{F}$ of formulas and $D$, the problem $\mathrm{DataSat}(\mathcal{F}, D)$ asks, given a finite set $\Sigma$ and a sentence $\varphi \in \mathcal{F}[\Sigma, D]$, whether some $\mathfrak{A} \in \mathrm{Data}[\Sigma, D]$ satisfies $\varphi$. Models are finite.

## Depends on

None.

## Proof depends on

None.

## Expansion

The local modality restricts what a formula can say about distant data, which is why fragments with small radius stay decidable: the existential fragment of radius $1$ is NEXPTIME-complete for every $D \geq 1$, and radius $2$ with two data values is N2EXPTIME-complete. Full $\mathrm{dFO}$ with two data values is undecidable already without unary predicates and without the mixed relations $\sim_{1,2}$, $\sim_{2,1}$, since it can describe finite structures with two equivalence relations (Janiczak).

## Sources

- B. Bollig, A. Sangnier and O. Stietel, "On the existential fragments of local first-order logics with data", in *Proceedings of GandALF 2022*, Electronic Proceedings in Theoretical Computer Science 370, 2022, pp. 1–16, doi:10.4204/EPTCS.370.1; read as arXiv:2209.10309v1, <https://arxiv.org/abs/2209.10309v1>: Section 2 (data structures, first-order logic, data graphs, views, local first-order logic and its existential fragment, and the satisfiability problem) and Theorems 1–5.
