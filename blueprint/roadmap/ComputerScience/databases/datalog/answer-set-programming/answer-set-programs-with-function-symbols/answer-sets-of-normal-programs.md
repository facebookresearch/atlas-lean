# Answer sets of normal programs with function symbols

A normal logic program with function symbols is grounded over its Herbrand universe, possibly into infinitely many ground rules; an answer set is a model of the grounding in which every atom is derived by a rule from atoms proven earlier in some well-founded order.

**Ground programs.** A *ground rule* $r$ has the form $b \leftarrow a_1, \dots, a_m, \neg a_{m+1}, \dots, \neg a_n$ or $\leftarrow a_1, \dots, a_m, \neg a_{m+1}, \dots, \neg a_n$ (a *constraint*), with $0 \le m \le n$ and propositional atoms $b, a_i$. Write $H_r$ for the set of head atoms (at most one), $B_r^+ = \{a_1, \dots, a_m\}$ and $B_r^- = \{a_{m+1}, \dots, a_n\}$. A ground program is a set of ground rules. An interpretation $I$ (a set of atoms) *satisfies* $r$ if $(H_r \cup B_r^-) \cap I \ne \emptyset$ or $B_r^+ \not\subseteq I$, and is a *model* of a ground program if it satisfies all its rules. A model $I$ of a ground program $P$ is an *answer set* of $P$ if there is a function $\varphi \colon I \to \mathbb N$ such that every $a \in I$ is *proven*: some rule $r \in P$ with $H_r = \{a\}$ has $B_r^+ \subseteq I$, $B_r^- \cap I = \emptyset$ and $\varphi(b) < \varphi(a)$ for all $b \in B_r^+$.

**Programs with function symbols.** Fix disjoint countably infinite sets of predicates, function symbols, constants and variables, predicates and function symbols having arities. Terms are built from constants and variables by function symbols. A *(non-ground) program* is a finite set of rules of the same shape, with atoms $p(\vec t)$ over terms in place of propositional atoms; rules are *safe*: every variable of a rule occurs in a positive body atom. The Herbrand universe $\mathrm{HU}(P)$ is the set of ground terms built from the constants and function symbols of $P$; $\mathrm{Ground}(P)$ is the (possibly infinite) set of all instances of rules of $P$ under substitutions into $\mathrm{HU}(P)$. An *answer set* of $P$ is an answer set of $\mathrm{Ground}(P)$.

**Properties.** $P$ is *consistent* if it has an answer set. $P$ is *frugal* if all its answer sets are finite, and *non-proliferous* if it has only finitely many finite answer sets (it may have arbitrarily many infinite ones).

## Depends on

None.

## Proof depends on

None.

## Expansion

This is the stable model semantics of Gelfond and Lifschitz, phrased through levels of proof: requiring each atom to be supported by a rule whose positive body atoms come earlier rules out self-supporting loops. For ground programs consistency is NP-complete, and for function-free non-ground programs it is NEXPTIME-complete; with function symbols the grounding can be infinite and the problem leaves the arithmetical hierarchy. Not every frugal program is non-proliferous: a program can generate finite chains of every length, each closed off by a marker atom, while a constraint kills the infinite chain.

## Sources

- Lukas Gerlach, David Carral and Markus Hecher, "Finite Groundings for ASP with Functions: A Journey through Consistency", in *Proceedings of the Thirty-Third International Joint Conference on Artificial Intelligence (IJCAI 2024)*, 2024, pp. 3386–3394, <https://doi.org/10.24963/ijcai.2024/375>; read as arXiv:2405.15794v1, <https://arxiv.org/abs/2405.15794v1>: the Preliminaries (ground and non-ground ASP) and the definition of frugal and non-proliferous programs in Section 4 of that version.
