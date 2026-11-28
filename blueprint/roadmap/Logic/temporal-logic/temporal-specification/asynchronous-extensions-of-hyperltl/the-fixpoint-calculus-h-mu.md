# The fixpoint calculus H_μ for asynchronous hyperproperties

H_μ combines the path quantifiers of HyperLTL with a linear-time μ-calculus whose next operator is indexed by a path, so that the quantified paths can be advanced independently and compared asynchronously.

**Syntax.** Fix a finite set $AP$ of atomic propositions, path variables $\pi_1,\dots,\pi_n$ and predicate variables $X_1,\dots,X_m$. Formulas of $H_\mu$ are defined by the grammar

$$
\varphi::=\exists\pi.\varphi\mid\forall\pi.\varphi\mid\psi,\qquad\psi::=a_\pi\mid X\mid\bigcirc_\pi\psi\mid\psi\vee\psi\mid\neg\psi\mid\mu X.\psi,
$$

with $a\in AP$. In $\mu X.\psi$ every occurrence of $X$ lies under an even number of negations and directly under some $\bigcirc_\pi$ (strict guardedness); a formula is *closed* if all path and predicate variables are bound. The greatest fixpoint $\nu X.\psi$ and the operators $\mathcal G_\pi\psi\equiv\nu X.(\psi\wedge\bigcirc_\pi X)$ and $\mathcal F_\pi\psi\equiv\mu X.(\psi\vee\bigcirc_\pi X)$ are definable.

**Semantics.** Formulas are evaluated over a [Kripke structure](../kripke-structures-with-initial-states.md) $\mathcal K=(S,s_0,\delta,L)$ with finitely many states. A path assignment $\Pi$ maps the free path variables to paths of $\mathcal K$ from $s_0$, and a quantifier-free formula denotes a set of position vectors $(j_1,\dots,j_n)\in\mathbb N^n$, one position on each path: $a_{\pi_i}$ is true at $(j_1,\dots,j_n)$ if $a\in L(\Pi(\pi_i)(j_i))$, $\bigcirc_{\pi_i}\psi$ is true if $\psi$ is true at the vector in which only $j_i$ is increased by $1$, the Boolean connectives are set operations, and $\mu X.\psi$ denotes the least fixpoint. A quantifier-free formula is true under $\Pi$ if it is true at $(0,\dots,0)$, and $\exists\pi$, $\forall\pi$ range over the paths of $\mathcal K$. Because each $\bigcirc_\pi$ advances only one path, a step on one path may be matched by any number of steps on another.

For a closed formula $\varphi$, *model checking* asks whether $\mathcal K\models\varphi$, and *satisfiability* asks whether some non-empty set of traces satisfies $\varphi$, with the quantifiers then ranging over that set. $H_\mu$ subsumes [HyperLTL](../hyperltl.md), whose temporal operators advance all paths synchronously, and it is built on the linear-time μ-calculus, whose fixpoints it evaluates on vectors of positions.

## Depends on

- [Kripke structures with initial states](../kripke-structures-with-initial-states.md)

## Proof depends on

None.

## Sources

- J. O. Gutsfeld, M. Müller-Olm and C. Ohrem, "Automata and fixpoints for asynchronous hyperproperties", *Proceedings of the ACM on Programming Languages* 5(POPL), pp. 1–29, 2021, doi:[10.1145/3434319](https://doi.org/10.1145/3434319); read in arXiv:2010.11605v1 ([arXiv](https://arxiv.org/abs/2010.11605v1)), whose numbering is used: the definitions of Kripke structures in the preliminaries, and the syntax, constraints, path and quantifier semantics and decision problems in the section "A μ-calculus for Hyperproperties".
