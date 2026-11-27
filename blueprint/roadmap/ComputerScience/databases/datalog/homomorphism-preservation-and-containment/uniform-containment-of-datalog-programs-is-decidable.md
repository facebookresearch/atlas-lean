# Uniform containment of Datalog programs is decidable

For Datalog programs $P$ and $P'$ with the same extensional relations and the same intensional relations, $P$ is uniformly
contained in $P'$ when
$P(I) \subseteq P'(I)$ for every instance $I$ over the whole schema of $P$, extensional and intensional relations alike.
Uniform containment implies containment with respect to every common intensional relation, but not conversely.

**Theorem.** Uniform containment of Datalog programs is decidable, whereas containment is undecidable.

## Depends on

- [Datalog programs and the immediate consequence operator](../datalog-programs-and-the-immediate-consequence-operator.md)
- [Containment of Datalog queries is undecidable](../containment-of-datalog-queries-is-undecidable.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, *Foundations of Databases*, Addison-Wesley, 1995; authors' web edition <http://webdam.inria.fr/Alice/pdfs/all.pdf>, Section 12.5 (uniform containment, pp. 303–304), Exercises 12.27 and 12.28 and the bibliographic notes, crediting Cosmadakis and Kanellakis and Sagiv.
