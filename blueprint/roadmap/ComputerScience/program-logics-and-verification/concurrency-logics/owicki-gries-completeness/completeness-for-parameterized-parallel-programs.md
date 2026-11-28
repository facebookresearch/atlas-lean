# Semantic completeness of the Owicki–Gries system for parameterized programs

Extending the Owicki–Gries system by a rule for programs $\Vert_{i=1}^{n} S(i, n)$ of $n$ instances of one parameterized component gives a semantically complete system: every specification valid for all $n$ has a single proof outline, with assertions sets of states parameterized by $n$ and $i$, that works for every $n$.

A *parameterized component program* $S(i, n)$ is a component program of the [Owicki–Gries proof system](owicki-gries-system-with-auxiliary-variables.md) whose expressions may use two special variables standing for the parameters $n \in \mathbb{N}$ and $i \in \{1, \dots, n\}$, and array (composed) variables $y[a]$ besides simple variables, all values being natural numbers. For each $n$, $\Vert_{i=1}^{n} S(i, n)$ denotes the parallel program $S(1, n) \parallel \dots \parallel S(n, n)$. The system $\mathcal{F}$ adds to $\mathcal{O}$ the rule: if for every $i$ with $1 \le i \le n$ the proof outline $\{P(i, n)\}\,S(i, n)\,\{Q(i, n)\}$ is derivable, and for all $i \ne j$ in $\{1, \dots, n\}$ the proof outlines for $i$ and $j$ are interference free, then

$$\vdash_{\mathcal{F}} \Big\{\bigcap_{i=1}^{n} P(i, n)\Big\}\ \Vert_{i=1}^{n} S(i, n)\ \Big\{\bigcap_{i=1}^{n} Q(i, n)\Big\}.$$

A parameterized triple $\{P(n)\}\,\Vert_{i=1}^{n} S(i, n)\,\{Q(n)\}$ is *valid*, $\models_{\mathcal{F}}$, if $\models \{P(n)\}\,\Vert_{i=1}^{n} S(i, n)\,\{Q(n)\}$ holds in the sense of partial correctness for every $n$.

**Theorem (semantic completeness).** Take assertions to be sets of states. If $\models_{\mathcal{F}} \{P(n)\}\,\Vert_{i=1}^{n} S(i, n)\,\{Q(n)\}$, then there is an annotation $A$ of the history-instrumented components $S^\ast(i, n)$, assigning to each control point a set of states depending on $n$ and $i$, such that $\vdash_{\mathcal{F}} \{P(n)\}\ z := \lceil\,\rceil;\ \Vert_{i=1}^{n} A(S^\ast(i, n))\ \{Q(n)\}$; deleting the auxiliary variable $z$ gives $\vdash_{\mathcal{F}} \{P(n)\}\,\Vert_{i=1}^{n} S(i, n)\,\{Q(n)\}$.

Completeness of $\mathcal{O}$ gives, for each $n$ separately, some proof outlines; the theorem gives one uniform family, instantiated by the value of $n$.

## Depends on

- [Owicki–Gries proof system with auxiliary variables](owicki-gries-system-with-auxiliary-variables.md)

## Proof depends on

- [Owicki–Gries proof system with auxiliary variables](owicki-gries-system-with-auxiliary-variables.md)
- [Reachability annotations give interference-free proof outlines](reachability-annotations-are-interference-free.md)

## Expansion

The source sets the annotation at control point $j$ of component $i$ to the reachable-state set that the completeness construction for $\mathcal{O}$ assigns to the concrete program with $n$ components, so the four conditions for each $n$ reduce to those of the concrete program. Section 4 of the source adds an expressiveness argument in elementary arithmetic for relative completeness; this page states the semantic result of Section 3 only. A development needs the syntax and semantics of parameterized programs (the special parameter variables, arrays coded as natural numbers, the substitution $S \mapsto S(i, n)$) and the generalization of the reachability lemma to annotations with the parameters free.

## Sources

- L. Prensa Nieto, "Completeness of the Owicki-Gries system for parameterized parallel programs", in *Proceedings 15th International Parallel and Distributed Processing Symposium (IPDPS 2001)*, workshop on Formal Methods for Parallel Programming: Theory and Applications, IEEE, 2001, pp. 1534–1541, <https://doi.org/10.1109/IPDPS.2001.925138>, author copy <https://www-sop.inria.fr/lemme/Leonor.Prensa/publications/Compl.ps.gz>: Section 1 (the rule for parameterized programs and the system $\mathcal{F}$), Section 2 (syntax, semantics and Definitions 2.1 and 2.2), Section 3 (semantic completeness: conditions (a)–(d), the uniform annotation $r_j(i, n) = r^n_{ji}$, and "This closes our proof of semantic completeness of the system F").
- T. Nipkow and L. Prensa Nieto, "Owicki/Gries in Isabelle/HOL", in *Fundamental Approaches to Software Engineering (FASE 1999)*, LNCS 1577, Springer, 1999, <https://www21.in.tum.de/~nipkow/pubs/fase99.html>: not consulted; cited by Prensa Nieto, Section 1, for the soundness of $\mathcal{F}$.
