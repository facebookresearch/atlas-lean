# Progressing, connected and established entailment problems

An entailment problem asks whether every heap model of a quantifier-free separation-logic formula is a model of a second formula, where predicates are defined by inductive rules. Progress, connectivity and establishment are syntactic restrictions on those rules, imposed on the left side, the right side or both.

**Formulas.** Fix a natural number $\kappa$ (the record size), a countably infinite set of predicate symbols, each with an arity, a countably infinite set of variables and a special constant $\bot$. Formulas are

$$
\phi ::= x \not\approx x' \mid x \approx x' \mid x \mapsto (y_1, \dots, y_\kappa) \mid p(x_1, \dots, x_n) \mid \phi_1 * \phi_2 \mid \phi_1 \vee \phi_2 \mid \exists x .\, \phi_1
$$

where $p$ has arity $n$, the $x$'s are variables and each $y_i$ is a variable or $\bot$. A symbolic heap is a formula $\exists \vec{x} .\, \alpha_1 * \dots * \alpha_m$ whose $\alpha_j$ are atoms (equational, points-to or predicate atoms); it is predicate-less if it has no predicate atom. A variable $x$ is allocated by a symbolic heap if the heap contains a chain of equalities $x = x_1 \approx x_2 \approx \dots \approx x_n$ ($n \ge 1$) and a points-to atom $x_n \mapsto (\dots)$.

**Inductive definitions.** A set of inductive definitions (SID) $\mathcal{R}$ is a finite set of rules $p(x_1, \dots, x_n) \Leftarrow \pi$ with pairwise distinct $x_1, \dots, x_n$ and a quantifier-free symbolic heap $\pi$; the variables of $\pi$ other than $x_1, \dots, x_n$ are the rule's existential variables. Replacing a predicate atom $p(u_1, \dots, u_n)$ in a formula by the body of a rule for $p$, with $x_i$ replaced by $u_i$ and existential variables renamed apart, is one unfolding step; an unfolding is the result of finitely many steps.

**Semantics.** Fix a countably infinite set of locations containing a special location for $\bot$. A structure $(s, h)$ is a store $s$, a partial map from variables and $\bot$ to locations that is defined on $\bot$ and maps $x$ to the location of $\bot$ exactly when $x = \bot$, and a heap $h$, a finite partial map from locations to $\kappa$-tuples of locations, undefined at the location of $\bot$. Satisfaction of a formula $\phi$ by $(s, h)$ requires that $s$ is defined on every free variable of $\phi$. Equational atoms hold in the empty heap when the store makes them true; $x \mapsto (y_1, \dots, y_\kappa)$ holds exactly in the one-cell heap mapping $s(x)$ to $(s(y_1), \dots, s(y_\kappa))$; $\phi_1 * \phi_2$ holds when the heap splits into two disjoint heaps satisfying $\phi_1$ and $\phi_2$; $\vee$ and $\exists$ are as usual; and $(s, h) \models_{\mathcal{R}} p(x_1, \dots, x_n)$ is the least relation such that some rule $p(x_1, \dots, x_n) \Leftarrow \pi$ of $\mathcal{R}$ and some store agreeing with $s$ on $x_1, \dots, x_n$ satisfy $\pi$ in $h$. Write $\phi \models_{\mathcal{R}} \psi$ when every structure satisfying $\phi$ satisfies $\psi$.

**Entailment problems.** An entailment problem is a triple $\phi \vdash_{\mathcal{R}} \psi$ with $\phi$ a quantifier-free formula, $\psi$ a formula and $\mathcal{R}$ an SID; it is valid if $\phi \models_{\mathcal{R}} \psi$.

**Restrictions.** A rule $p(x_1, \dots, x_n) \Leftarrow \pi$ is

- progressing if $\pi = x_1 \mapsto (y_1, \dots, y_\kappa) * \rho$ where $\rho$ has no points-to atom;
- connected if it is progressing with $\pi = x_1 \mapsto (y_1, \dots, y_\kappa) * \rho$ and every predicate atom of $\rho$ has the form $q(y_i, \vec{u})$ for some $i \in \{1, \dots, \kappa\}$;
- established if every existential variable of the rule is allocated by every predicate-less unfolding of $\pi$.

$\mathcal{R}$ is progressing (connected, established) for a formula $\phi$ if every rule for every predicate on which a predicate of $\phi$ depends, itself included, is progressing (connected, established). The problem $\phi \vdash_{\mathcal{R}} \psi$ is left-progressing (left-connected, left-established) if $\mathcal{R}$ has that property for $\phi$, right-progressing (and so on) if it has it for $\psi$, and progressing (connected, established) if it is both left- and right-progressing (connected, established).

A progressing rule allocates exactly the first parameter of its head and nothing else directly, so every unfolding step adds one heap cell. Connectivity makes the cells allocated by a predicate form a tree reachable from its first parameter. Establishment forces every existentially introduced variable to name an allocated cell. The progressing, connected and left-established entailment problems are decidable and complete for doubly exponential time (Theorem 5 of the report version cited below). The same report shows that dropping right-connectivity makes the problem undecidable.

## Depends on

None.

## Proof depends on

None.

## Sources

- Mnacho Echenim, Radu Iosif and Nicolas Peltier, "Unifying Decidable Entailments in Separation Logic with Inductive Definitions", in *Automated Deduction – CADE 28*, Lecture Notes in Computer Science 12699, pp. 183–199, Springer, 2021, <https://doi.org/10.1007/978-3-030-79876-5_11>; read in arXiv:2012.14361v2, <https://arxiv.org/abs/2012.14361v2> (the report version): Section 2 (syntax, Definition 1 of allocation, SIDs, unfoldings, semantics, Definition 3 of entailment problems) and Definition 4 (progressing, connected and established rules and problems) of that version.
