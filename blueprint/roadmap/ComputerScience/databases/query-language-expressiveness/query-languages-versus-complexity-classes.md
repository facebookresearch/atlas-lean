# Query languages versus complexity classes (fixpoint and while queries)

This node collects the language-equivalence and capture results for fixpoint and while queries in two
frameworks that the expansion keeps separate: the active-domain, partial semantics of Abiteboul, Hull and
Vianu, and the finite-structure, total semantics of Libkin.

## Expansion

A sound expansion has separate pages for:

1. **Active-domain framework.** Fixpoint queries equal CALC+$\mu^+$, while$^+$ and Datalog with negation
   under inflationary semantics (Theorem 14.4.5); while queries equal CALC+$\mu$, while and Datalog with
   negation under noninflationary semantics (Theorem 14.4.6). On ordered databases with a successor
   relation on the active domain, fixpoint $=$ QPTIME and while $=$ QPSPACE (17.4.2); on unordered
   databases, while $=$ fixpoint if and only if PTIME $=$ PSPACE (17.4.3), as reported by the source,
   whose treatment of divergent while queries is recorded on the page.
2. **Finite-structure framework.** Quantifiers range over the universe and partial fixed points are total
   (empty on non-stabilization). Over finite structures with a built-in linear order,
   LFP $=$ IFP $=$ PTIME (10.12, 10.14; for ordered graphs this is the
   [Immerman–Vardi theorem](../../../TheoryOfComputation/descriptive-complexity/immerman-vardi-theorem/immerman-vardi.md))
   and PFP $=$ PSPACE (10.15); and LFP $=$ PFP if and only if PTIME $=$
   PSPACE, with the ordered and unordered clauses of 11.26–11.27.
3. **Inflationary versus stratified semantics** are distinct: stratified Datalog with negation expresses
   strictly fewer queries than the fixpoint queries (15.4.2); the ordered characterization of
   stratified Datalog with negation (15.4.8) is a separate result.
4. **Comparison bridge,** unproved and kept separate: an agreement lemma between the two frameworks must
   align the structure universe with the active domain, the quantifier interpretation and the
   empty-domain convention, and restrict to inputs on which the partial queries are defined. It also needs
   an order adapter between the two clauses on order: a successor relation is first-order definable from a
   finite linear order, and the linear order is definable from the successor relation by an inflationary
   fixpoint (transitive closure).

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Deterministic/nondeterministic time and space classes.
- Statement prerequisite: Logics over finite structures as query languages.
- Statement prerequisite: query complexity classes defined through recognition problems (the first source's Section 16.3).
- Statement prerequisite: the syntax of Datalog with negation, shared with
  [stratified Datalog with negation](../datalog/stratified-datalog-with-negation.md).

## Depends on

- [Relational calculus and domain independence](../relational-calculus/relational-calculus-and-domain-independence.md)

## Sources

- Foundations of Databases (Abiteboul, Hull, Vianu) — Abiteboul, Hull, Vianu; authors' free web edition (webdam.inria.fr/Alice). <http://webdam.inria.fr/Alice/pdfs/all.pdf>
- Elements of Finite Model Theory (Libkin) — Leonid Libkin. <https://www.cs.utoronto.ca/~libkin/fmt/fmt.pdf>
