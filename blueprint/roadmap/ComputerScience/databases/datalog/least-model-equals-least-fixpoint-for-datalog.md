# Least model equals least fixpoint for Datalog

Let $P$ be a Datalog program and $I$ an instance over its extensional predicates, and let $T_P$ be the
immediate-consequence operator. Then $T_P$ has a least fixpoint containing $I$, it equals the minimal model
$P(I)$ of $P$ containing $I$, and

$$T_P^\omega(I) = P(I).$$

Since only finitely many facts over the active domain exist, naive iteration of $T_P$ from $I$ stabilizes
after at most as many steps as there are possible intensional facts, a number polynomial in the size of
the active domain for fixed $P$.

## Depends on

- [Datalog programs and the immediate consequence operator](datalog-programs-and-the-immediate-consequence-operator.md)

## Proof depends on

- [The immediate consequence operator is monotone](fixpoint-semantics/the-immediate-consequence-operator-is-monotone.md)
- [Models of a Datalog program are the pre-fixpoints of its immediate consequence operator](fixpoint-semantics/models-of-a-datalog-program-are-pre-fixpoints-of-tp.md)
- [A Datalog program has a minimum model containing its input](fixpoint-semantics/a-datalog-program-has-a-minimum-model-containing-its-input.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995 (authors' web edition), Theorems 12.3.2 and 12.3.4. <http://webdam.inria.fr/Alice/pdfs/all.pdf>
