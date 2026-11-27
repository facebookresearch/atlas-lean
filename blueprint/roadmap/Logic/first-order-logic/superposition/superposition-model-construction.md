# Model construction for superposition

Let $N$ be a set of clauses that is [saturated up to redundancy](redundancy-and-fair-runs-for-superposition.md) and does not contain the empty clause, and let $E_C$, $R_C$ and $R_\infty$ be its [candidate interpretation](candidate-interpretation-for-superposition.md). Then for every ground instance $C\theta \in G_\Sigma(N)$:

1. $E_{C\theta} = \emptyset$ if and only if $C\theta$ is true in $R_{C\theta}$;
2. if $C\theta$ is redundant with respect to $G_\Sigma(N)$, then it is true in $R_{C\theta}$;
3. $C\theta$ is true in $R_\infty$ and in $R_D$ for every $D \in G_\Sigma(N)$ with $D \succ_C C\theta$.

**Proof sketch.** Induction on $\succ_C$. Redundant clauses follow from smaller true clauses; if a variable instance $x\theta$ is reducible by $R_{C\theta}$, a smaller instance has the same truth value; otherwise a non-productive false clause yields, by saturation and the lifting lemmas, an equality resolution, equality factoring or superposition inference whose conclusion is a smaller false clause.

## Depends on

- [Redundancy and fair runs for superposition](redundancy-and-fair-runs-for-superposition.md)
- [Candidate interpretation for superposition](candidate-interpretation-for-superposition.md)

## Proof depends on

- [Candidate rewrite systems are convergent](candidate-rewrite-systems-are-convergent.md)
- [Lifting lemmas for superposition](lifting-lemmas-for-superposition.md)

## Sources

- U. Waldmann, *Automated Reasoning II*, lecture notes, Max Planck Institute for Informatics, summer semester 2024, <https://rg1-teaching.mpi-inf.mpg.de/autrea2-ss24/notes-current.pdf>, Section 3.4, Lemma 3.4, Corollaries 3.5 and 3.6, lifting Lemmas 3.7 and 3.8, and Theorem 3.9 ("Model Construction") with its proof, pp. 55–59.
