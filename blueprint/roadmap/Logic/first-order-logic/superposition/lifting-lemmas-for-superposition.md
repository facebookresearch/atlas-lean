# Lifting lemmas for superposition

Use the inferences, orderings and conventions of the [superposition calculus](superposition-calculus.md).

1. Let $C$ be a clause and $\theta$ a substitution such that $C\theta$ is ground. Then every equality resolution or equality factoring inference from $C\theta$ is a ground instance of an inference from $C$.
2. Let $D = D' \vee u \approx v$ and $C = C' \vee [\neg]\, s \approx t$ be clauses without common variables, and $\theta$ a substitution such that $D\theta$ and $C\theta$ are ground. If there is a superposition inference from $D\theta$ and $C\theta$ in which $u\theta$ is overlapped with a subterm of $s\theta$, and $u\theta$ does not occur in $s\theta$ at or below a variable position of $s$, then this inference is a ground instance of a superposition inference from $D$ and $C$.

**Proof idea.** The ground inference unifies two terms, so $\theta$ is a unifier of the corresponding non-ground terms and factors through their most general unifier $\sigma$, say $\theta = \sigma\rho$; the ordering conditions that hold after applying $\theta$ imply the weaker conditions required after applying $\sigma$, because the orderings are stable under substitutions. In part 2 the condition on variable positions ensures that the overlapped subterm of $s\theta$ is an instance of a non-variable subterm of $s$.

## Depends on

- [Superposition calculus](superposition-calculus.md)

## Proof depends on

- [Unification returns a most general unifier](../first-order-unification/is-mgu-unify.md)

## Sources

- U. Waldmann, *Automated Reasoning II*, lecture notes, Max Planck Institute for Informatics, summer semester 2024, <https://rg1-teaching.mpi-inf.mpg.de/autrea2-ss24/notes-current.pdf>, Section 3.4, Lemmas 3.7 and 3.8 ("Lifting Lemma"), p. 56, whose proofs are left as exercises there.
