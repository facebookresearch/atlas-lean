# A three-valued evaluation with certainty guarantees for first-order queries

Consider incomplete databases whose entries are constants or nulls, and for a first-order query $\varphi(\bar x)$
let $\mathrm{cert}(\varphi, D)$ be the set of tuples of constants that are answers to $\varphi$ on every complete
database obtained from $D$ by replacing the nulls with constants. Two tuples over constants and nulls unify if some
assignment of the nulls makes them equal.

Let $\mathrm{Eval}_{3v}$ be the evaluation with truth values $0, \tfrac12, 1$ that interprets connectives and
quantifiers over the active domain in the usual three-valued way (minimum, maximum, $1 - x$) and atoms as follows:
$R(\bar x)$ is $1$ if $\nu(\bar x) \in R^D$, $0$ if $\nu(\bar x)$ unifies with no tuple of $R^D$, and $\tfrac12$
otherwise; $x = y$ is $1$ if $\nu(x) = \nu(y)$, $0$ if $\nu(x), \nu(y)$ are distinct constants, and $\tfrac12$
otherwise. Then $\mathrm{Eval}_{3v}$ has certainty guarantees for every first-order query: for every database $D$ and
every tuple $\bar a$ of constants, if $\mathrm{Eval}_{3v}$ evaluates $\varphi(\bar a)$ to $1$ then
$\bar a \in \mathrm{cert}(\varphi, D)$.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Statement prerequisite: Incomplete databases, possible worlds and certain answers.
- Statement prerequisite: SQL nulls and three-valued logic.

## Sources

- L. Libkin, *SQL's three-valued logic and certain answers*, ACM Trans. Database Syst. 41(1) (2016), §3, Definition 3.1, the atom rules for the evaluation procedure, and Theorem 4.1. <https://homepages.inf.ed.ac.uk/libkin/papers/tods16.pdf>
