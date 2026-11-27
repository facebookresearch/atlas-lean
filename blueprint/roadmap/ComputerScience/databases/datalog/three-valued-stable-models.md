# 3-stable models of Datalog programs with negation

A 3-valued instance assigns to each ground fact over the schema of a Datalog program with negation $P$ a truth value
in $\{0, \tfrac12, 1\}$; instances are compared pointwise in the truth order $0 < \tfrac12 < 1$, so the least instance
$\bot$ makes every fact false. For an input instance $I$, all constructions below use the program $P_I$ obtained from $P$ by adding a
unit rule $A \leftarrow$ for each fact $A$ of $I$, so that input facts are supported; ground instances of rules range
over the constants of $P$ and of $I$, and $P^{\mathrm{wf}}(I)$ denotes the well-founded semantics of $P_I$. A 3-valued
instance $I$ gives a value $\hat I$ to literals and bodies: $\hat I(A) = I(A)$, $\hat I(\neg A) = 1 - I(A)$, a truth
value is its own value, and a conjunction takes the minimum of the values of its members. A 3-extended program is a
program without negation whose rule bodies may also contain truth values; its 3-valued immediate-consequence operator
maps $J$ to the 3-valued instance that gives each ground fact $A$ the maximum of $\hat J(\mathrm{body})$ over the ground
rules with head $A$, and $0$ if there is none. It is monotone, and its least fixpoint, the limit of its iteration from
$\bot$, is the least 3-valued model of the program. For a 3-valued instance $I$, the positivized ground program
$\mathrm{pg}(P, I)$ replaces each negative premise $\neg A$ of the ground instances of $P$ by the truth value
$\hat I(\neg A)$; it is a 3-extended program, and $\mathrm{conseq}_P(I)$ is its least 3-valued model. A 3-stable model of
$P$ is a 3-valued instance $I$ with $\mathrm{conseq}_P(I) = I$, and the well-founded semantics $P^{\mathrm{wf}}$ consists
of the positive and negative facts common to all 3-stable models of $P$. A total 3-stable model, one with no value
$\tfrac12$, is a stable model of $P$.

## Depends on

- [Datalog programs and the immediate consequence operator](datalog-programs-and-the-immediate-consequence-operator.md)

## Proof depends on

- [Least model equals least fixpoint for Datalog](least-model-equals-least-fixpoint-for-datalog.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, the program $P_I$ (p. 387), the value $\hat I$ of literals and bodies and the 3-valued immediate consequence operator (pp. 387–388), Lemma 15.3.4 (pp. 388–389), Definitions 15.3.5 and 15.3.7 (pp. 389–390), and the bibliographic notes to Chapter 15 relating total 3-stable models to stable models (p. 408).
