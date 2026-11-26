# Lopsided Moser-Tardos theorem

In the variable model, call events $A_i$ and $A_j$ *lopsidependent* if there are assignments $f, g$ agreeing outside $\mathrm{vbl}(A_i) \cap \mathrm{vbl}(A_j)$ with $f \in A_i$, $g \in A_j$, and $f \notin A_j$ or $g \notin A_i$. Events with disjoint variable sets are never lopsidependent. If $x_i \in [0,1)$ satisfy $\Pr[A_i] \le x_i \prod_{j \in \Gamma'(i)} (1 - x_j)$, where $\Gamma'(i)$ contains every event lopsidependent with $A_i$, then the conclusions of the Moser-Tardos theorem hold: at most $x_i/(1-x_i)$ expected resamplings of $A_i$ under every valid rule, almost-sure termination, and an assignment avoiding all events. The symmetric specialization holds with $d$ the maximum number of lopsidependent neighbors.

## Proof sketch

Build witness trees with respect to lopsidependence. Consecutive resamplings of non-lopsidependent events can be commuted without changing the run's checks, so a log can be normalized to a canonical depth-ordered form; the witness tree lemma then holds with lopsidependence in place of adjacency, and the counting argument is unchanged.

## Depends on

- [Moser-Tardos resampling algorithm in the variable model](moser-tardos-algorithm.md)

## Proof depends on

- [Moser-Tardos witness tree lemma](moser-tardos-witness-tree-lemma.md)
- [Moser-Tardos theorem: the resampling algorithm finds an assignment avoiding all events](moser-tardos-theorem.md)

## Sources

- Robin A. Moser and Gábor Tardos, "A Constructive Proof of the General Lovász Local Lemma", Journal of the ACM 57(2), 2010.
