# Datalog evaluation is EXPTIME-complete in combined complexity

A Datalog query $q = (\Pi, R)$ consists of a Datalog program $\Pi$ and an intensional relation name $R$ of $\Pi$; on
a database $D$ over the extensional relation names of $\Pi$ it returns $q(D) = \{\bar a : R(\bar a) \in \Pi(D)\}$,
where $\Pi(D)$ is the least model of $\Pi$ containing $D$.

The problem Datalog-Evaluation, which asks for a Datalog query $q = (\Pi, R)$, a database $D$ over the extensional
relation names of $\Pi$ and a tuple $\bar a$ whether $\bar a \in q(D)$, with all three as input, is EXPTIME-complete.
The upper bound comes from computing $\Pi(D)$ by at most $\lvert \mathrm{sch}(\Pi) \rvert \cdot \lvert \mathrm{Dom}(D) \rvert^{\mathrm{ar}(\Pi)}$
applications of the immediate-consequence operator, where $\mathrm{ar}(\Pi)$ is the largest arity of a relation name of
$\Pi$; hardness is by a polynomial-time encoding of exponential-time deterministic Turing machines.

## Depends on

- [Datalog programs and the immediate consequence operator](datalog-programs-and-the-immediate-consequence-operator.md)
- [The class EXP](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/exp.md)
- [Polynomial-time many-one reduction](../../../TheoryOfComputation/np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md)

## Proof depends on

- [Least model equals least fixpoint for Datalog](least-model-equals-least-fixpoint-for-datalog.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Definition 35.16 and Proposition 35.17 (p. 319), the analysis before Theorem 37.1 and Theorem 37.1 (pp. 329–330).
