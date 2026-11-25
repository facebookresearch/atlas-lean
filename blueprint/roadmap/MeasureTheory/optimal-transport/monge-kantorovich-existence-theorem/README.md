# Monge–Kantorovich existence theorem

Let $X$ and $Y$ be Polish spaces, $P$ and $Q$ Borel probability measures on them, and
$c : X \times Y \to [0, \infty]$ continuous. Then some coupling $\pi$ of $P$ and $Q$ minimises the
total cost: $\int c \, d\pi \le \int c \, d\pi'$ for every coupling $\pi'$ of $P$ and $Q$.

## Idea

Monge looked for an optimal transport map, which need not exist: a Dirac mass cannot be split by a
map. Kantorovich allowed couplings, which may split mass, and then an optimal plan exists by the
direct method of the calculus of variations. The couplings of $P$ and $Q$ form a nonempty set,
containing $P \otimes Q$; it is tight because its marginals are fixed, hence relatively compact by
Prokhorov's theorem, and it is closed for weak convergence. The total cost is lower semicontinuous
for weak convergence because $c$ is continuous and nonnegative, so it attains its minimum on this
compact set.

## Statements

- [Monge–Kantorovich existence theorem](monge-kantorovich-exists.md)
- [Existence of an optimal coupling](exists-is-coupling-forall-lintegral-le.md): the same theorem stated for the coupling predicate, from which the main statement is deduced.
- [Optimal couplings exist for the Wasserstein cost](exists-is-coupling-lintegral-eq-transpor.md): a special case, the cost $d^p$.
- [Couplings](couplings.md): a definition used in the statement.
- [Couplings as sets and as predicates](mem-couplings-iff.md): relates the two descriptions of couplings.
- [Kantorovich cost](kantorovich-cost.md): a definition used in the statement.
- [The set of couplings is closed](is-closed-set-of-is-coupling.md): used in the proof.
- [Tightness of transference plans](is-tight-measure-set-set-of-is-coupling.md): used in the proof.
- [Lower semicontinuity of the total cost](lower-semicontinuous-lintegral.md): used in the proof.

## Sources

- C. Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen Wissenschaften 338, Springer, 2009, Chapter 4.
