# Tuple-independent probabilistic databases and query probability

Fix a relational vocabulary. A tuple-independent probabilistic database (probabilistic structure) is a pair
$(A, p)$ of a finite structure $A$ and a map $p$ assigning to each tuple $t$ of $A$ a rational probability
$p(t) \in [0, 1]$. It induces a probability distribution on the substructures $B$ of $A$ (the possible worlds,
obtained by keeping a subset of the tuples) by

$$p(B) = \prod_{t \in B} p(t) \prod_{t \in A \setminus B} \big(1 - p(t)\big),$$

so tuples are present independently. The probability of a Boolean query $q$ is
$p(q) = \sum_{B \subseteq A,\ B \models q} p(B)$. For a fixed Boolean query $q$, the evaluation problem asks, given
$(A, p)$, to compute $p(q)$; its complexity is measured in the size of $A$ and of the binary representations of the
numbers $p(t)$. For conjunctive queries $p(q)$ is computable in polynomial time with a $\#P$ oracle (the class
$\mathrm{FP}^{\#P}$). Since $p(q)$ is a rational number, the problem is not itself a $\#P$ function; the lower bounds for
it are $\#P$-hardness results.

## Depends on

- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [The counting class $\#P$](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/sharp-p.md)

## Sources

- N. Dalvi and D. Suciu, "The dichotomy of conjunctive queries on probabilistic structures", *Proceedings of the 26th ACM Symposium on Principles of Database Systems (PODS)*, 2007, pp. 293–302, Section 1, the problem EVALUATION and equation (1) (p. 293).
