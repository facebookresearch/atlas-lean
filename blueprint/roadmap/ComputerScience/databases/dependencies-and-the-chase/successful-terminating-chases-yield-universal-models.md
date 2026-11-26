# Successful terminating chases yield universal models

Let $\Sigma$ be a finite set of tuple-generating and equality-generating dependencies and $I$ a finite
instance. Suppose a restricted chase sequence from $I$ terminates successfully (no equality step tries to
equate two distinct constants) with result $J_0$. Then $J_0$ is a model of $\Sigma$, there is a
homomorphism from $I$ to $J_0$ that is the identity on constants (it may merge nulls, so $J_0$ need not
contain $I$ literally when equality steps fire), and for every model $J$ of $\Sigma$, finite or infinite,
with a constant-preserving homomorphism from $I$, there is a homomorphism $J_0 \to J$ that is the
identity on constants. Consequently $J_0$ is a universal model. For a union of conjunctive queries $q$, let the certain answers
of $q$ be the tuples of constants that belong to $q(J)$ for every model $J$ of $\Sigma$ with a
constant-preserving homomorphism from $I$; they are exactly the null-free tuples of $q(J_0)$. Failing chase sequences and
non-terminating ones are separate cases.

## Depends on

- [Tuple- and equality-generating dependencies and the chase](tuple-and-equality-generating-dependencies-and-the-chase.md)
- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Containment of unions of conjunctive queries](../conjunctive-queries/cores-and-minimization/containment-of-unions-of-conjunctive-queries.md)

## Proof depends on

- [Unions of conjunctive queries are preserved under homomorphisms](../conjunctive-queries/cores-and-minimization/unions-of-conjunctive-queries-are-preserved-under-homomorphisms.md)

## Sources

- Data Exchange: Semantics and Query Answering (Fagin, Kolaitis, Miller, Popa), TCS 2005, course copy — Theoretical Computer Science 336 (2005), Definitions 3.1–3.2 (restricted tgd steps, egd steps and failure, successful finite chases), Lemma 3.4 (a chase step preserves a homomorphism into an instance satisfying the dependency) and Theorem 3.3 with its proof (the data-exchange form), Proposition 4.2 (certain answers of unions of conjunctive queries on a universal solution). <https://www.cis.upenn.edu/~val/CIS650/DataX-tcs.pdf>
- Database Theory Lecture 19: The Chase (TU Dresden) — TU Dresden ICCL, Theorem 19.4 (the same induction for tuple-generating dependencies only). <https://iccl.inf.tu-dresden.de/w/images/5/54/Lecture-19-chase-4.pdf>
