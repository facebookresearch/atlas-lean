# SQL nulls and three-valued logic

This node collects the semantics of SQL nulls in a set-semantics fragment, following Libkin's formalization,
whose multiset extension is left open.

## Expansion

A sound expansion has separate pages for:

1. **Predicates.** Values are constants or a single unmarked null; comparisons involving null evaluate to
   unknown; AND, OR and NOT follow Kleene's strong three-valued logic on $\{t, f, u\}$ (minimum, maximum and
   negation with $f < u < t$); WHERE keeps tuples whose condition evaluates to $t$.
2. **Duplicate elimination and set operations** (UNION, INTERSECT, EXCEPT without ALL) compare tuples by
   syntactic equality, under which two nulls are equal, unlike predicate equality.
3. **Monotonicity.** The three-valued connectives are monotone in the information order with $u$ below $t$
   and $f$.
4. **Null-free agreement.** On databases without nulls, the SQL evaluation of the chosen set-semantics
   fragment coincides with two-valued evaluation.
5. The bag (multiset) extension, as a separate statement needing its own source.

## Depends on

- [Relational calculus and domain independence](../relational-calculus/relational-calculus-and-domain-independence.md)

## Related topics

- [Bag relations and bag relational algebra](bag-relations-and-bag-relational-algebra.md)

## Sources

- L. Libkin, *SQL's three-valued logic and certain answers*, ACM TODS 41(1), 2016, Section 1 (set semantics; the multiset extension left for future work) and Section 3 (the evaluation procedure $\mathrm{Eval}_{\mathrm{SQL}}$: comparisons with a null are unknown, connectives by minimum, maximum and $1 - x$, answers are the tuples evaluating to true, and $\mathrm{Eval}_{\mathrm{SQL}}$ coincides with two-valued evaluation over complete databases). <https://homepages.inf.ed.ac.uk/libkin/papers/tods16.pdf>
- P. Guagliardo and L. Libkin, *A formal semantics of SQL queries, its validation, and applications*, PVLDB 11(1), 2017, Section 1 (WHERE under Kleene's three-valued logic keeps the tuples evaluating to true; in set operations two values, including NULL, are equal when syntactically the same) and Section 3 (bag operations, duplicate elimination, and the set versions of UNION, INTERSECT and EXCEPT). <https://www.vldb.org/pvldb/vol11/p27-guagliardo.pdf>
