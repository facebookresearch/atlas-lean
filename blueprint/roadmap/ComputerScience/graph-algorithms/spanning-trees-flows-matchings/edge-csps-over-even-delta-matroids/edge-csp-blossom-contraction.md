# Blossom contraction preserves improvability

Let $f$ be a valid labeling of an edge CSP $I$ with even delta-matroid constraints and let $b$ be a blossom found by the forest search (after its preparation flip, if any), with defective base and set $L$ of constraints. **Contracting** $b$ deletes the internal variables of $b$, adds one new variable $v_C$ for each $C \in L$ and a new constraint $N$ on these variables whose relation is "exactly one $v_C$ is $1$", and replaces each $C \in L$ by the constraint on its remaining scope and $v_C$ that allows those tuples of $C$ agreeing with $f$ on all internal blossom variables of its scope (with $v_C = 0$) or differing from $f$ on exactly one of them (with $v_C = 1$). Then:

1. the contracted instance $I_b$ is an edge CSP with even delta-matroid constraints, at most as many variables as $I$ and one more constraint than $I$, and the induced labeling $f_b$ is valid with the same number of defects as $f$;
2. $f_b$ is optimal for $I_b$ if and only if $f$ is optimal for $I$;
3. from any valid labeling of $I_b$ with fewer defects than $f_b$ one computes in polynomial time a valid labeling of $I$ with fewer defects than $f$.

## Proof sketch

Each new constraint is the composition of the old one with a small even delta-matroid, so it is an even delta-matroid. If $f$ is not optimal, an augmenting walk for $f$ exists and is transported into $I_b$; conversely, an augmenting walk for $f_b$ is lifted through the blossom, using that every proper subwalk of a blossom is a valid flip.

## Depends on

- [Edge CSPs, occurrence labelings and defects](edge-csps-and-defects.md)
- [Delta-matroids and even delta-matroids](../../../../TheoryOfComputation/np-completeness/boolean-constraint-satisfaction/planar-boolean-csp/delta-matroids-and-even-delta-matroids.md)
- [Augmenting walks remove two defects](edge-csp-augmenting-walks.md)

## Proof depends on

- [Local contraction preserves even delta-matroids](../../../../TheoryOfComputation/np-completeness/boolean-constraint-satisfaction/planar-boolean-csp/local-contraction-preserves-even-delta-matroids.md)

## Sources

- A. Kazda, V. Kolmogorov and M. Rolínek, "Even Delta-Matroids and the Complexity of Planar Boolean CSPs", ACM Transactions on Algorithms 15(2), Article 22, 2019, Section 5.3, Observation 26, Theorem 24(2,4) and Lemmas 28, 29, 40.
