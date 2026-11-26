# 3-stable models of Datalog programs with negation

A 3-valued instance assigns to each ground fact over the schema of a Datalog program with negation $P$ a truth value
in $\{0, \tfrac12, 1\}$; instances are compared pointwise in the truth order $0 < \tfrac12 < 1$, so the least instance
makes every fact false. For a 3-valued instance $I$, the positivized ground program
$\mathrm{pg}(P, I)$ replaces each negative premise $\neg A$ of the ground instances of $P$ by the truth value of
$\neg A$ in $I$; it is a program without negation, and $\mathrm{conseq}_P(I)$ is its least 3-valued model, the least
fixpoint of its 3-valued immediate-consequence operator starting from the instance in which every fact is false. A
3-stable model of $P$ is a 3-valued instance $I$ with $\mathrm{conseq}_P(I) = I$, and the well-founded semantics
$P^{\mathrm{wf}}$ consists of the positive and negative facts common to all 3-stable models of $P$. A total
3-stable model, one with no value $\tfrac12$, is a stable model of $P$.

## Depends on

- [Datalog programs and the immediate consequence operator](datalog-programs-and-the-immediate-consequence-operator.md)

## Proof depends on

- [Least model equals least fixpoint for Datalog](least-model-equals-least-fixpoint-for-datalog.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Lemma 15.3.4 (pp. 387–389), Definitions 15.3.5 and 15.3.7 (pp. 389–390), and the bibliographic notes to Chapter 15 relating total 3-stable models to stable models (p. 408).
