# The calculus F-omega with type intervals

$F^\omega_{\cdot\cdot}$ extends Girard's $F^\omega$ with top and bottom types and replaces the kind of proper types by interval kinds $A..B$, inhabited by the types between $A$ and $B$; with dependent arrow kinds it expresses bounded quantification, bounded type operators and singleton kinds.

**Syntax.** Terms $s, t ::= x \mid \lambda x{:}A.\,t \mid s\,t \mid \lambda X{:}K.\,t \mid t\,A$. Types $A, B, C ::= X \mid \top \mid \bot \mid A \to B \mid \forall X{:}K.\,A \mid \lambda X{:}K.\,A \mid A\,B$. Kinds $J, K ::= A..B \mid (X{:}J) \to K$, where the dependent arrow kind binds $X$ in $K$; contexts $\Gamma ::= \emptyset \mid \Gamma, x{:}A \mid \Gamma, X{:}K$. One writes $*$ for $\bot..\top$ and $J \to K$ when $X$ is not free in $K$.

**Judgments.** The declarative system has mutually defined judgments for context formation, kind formation $\Gamma \vdash K\ \mathsf{kd}$, kinding $\Gamma \vdash A : K$, subkinding $\Gamma \vdash J \le K$, subtyping $\Gamma \vdash A \le B : K$ (subtyping is kinded), type and kind equality (each the conjunction of two subtyping or subkinding judgments), and typing $\Gamma \vdash t : A$. The subtyping rules are:

- reflexivity and transitivity, and subsumption along subkinding;
- $\Gamma \vdash \bot \le A : *$ and $\Gamma \vdash A \le \top : *$ whenever $\Gamma \vdash A : B..C$;
- contravariant–covariant arrows, $\forall$-types contravariant in the kind of the bound variable and covariant in the body, pointwise subtyping of operators $\lambda X{:}J_i.\,A_i$ at a common kind, and congruence for application with equal arguments;
- β- and η-conversion in both directions, at the appropriate kinds;
- **bound projection**: if $\Gamma \vdash A : B_1..B_2$ then $\Gamma \vdash B_1 \le A : *$ and $\Gamma \vdash A \le B_2 : *$;
- **interval introduction**: if $\Gamma \vdash A_1 \le A_2 : B..C$ then $\Gamma \vdash A_1 \le A_2 : A_1..A_2$.

Subkinding is contravariant–covariant on interval bounds and on arrow kinds. A singleton kinding rule narrows $\Gamma \vdash A : B..C$ to $\Gamma \vdash A : A..A$. The *subtyping problem* asks, given $\Gamma$, $A$, $B$ and $K$, whether $\Gamma \vdash A \le B : K$ is derivable.

## Depends on

None.

## Proof depends on

None.

## Expansion

Bounded quantification $\forall X \le B.\,A$ of $F_{<:}$ becomes $\forall X{:}\bot..B.\,A$, lower bounds use $A..\top$, and the singleton $A..A$ makes a type definition transparent. Bound projection reflects any assumed bounds into subtyping, including inconsistent ones: a variable of kind $\top..\bot$ in the context makes $\top \le \bot$ derivable. The source proves that this does not break type safety for closed terms. Its route goes through a normalization of types by hereditary substitution and an equivalent *canonical* system on β-normal, η-long types, in which subtyping can be inverted. The whole development is mechanized in Agda.

## Sources

- Sandro Stucki and Paolo G. Giarrusso, "A Theory of Higher-Order Subtyping with Type Intervals", *Proceedings of the ACM on Programming Languages* 5(ICFP), Article 69, 2021, 30 pages, <https://doi.org/10.1145/3473574>; read as the extended version arXiv:2107.01883v1, <https://arxiv.org/abs/2107.01883v1>: Section 2 ("Subtyping with Type Intervals") and Section 3 ("The Declarative System"), with Fig. 1 (syntax) and Figs. 3 and 4 (the declarative kinding and subtyping rules), in the numbering of that version.
