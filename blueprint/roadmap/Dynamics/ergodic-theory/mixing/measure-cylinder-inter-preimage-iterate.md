# A cylinder event is independent of the far future

Let $p$ be a probability measure on a measurable space $S$, let $\mu = p^{\mathbb{N}}$ be the product measure on
$S^{\mathbb{N}}$ and $\sigma$ the [left shift](shift.md). Let $s$ be a finite set of indices, all smaller than $n$,
and $A = \{x \in S^{\mathbb{N}} : (x_i)_{i \in s} \in C\}$ a cylinder event with $C \subseteq S^s$ measurable. Then
for every measurable $B \subseteq S^{\mathbb{N}}$,

$$\mu(A \cap \sigma^{-n} B) = \mu(A)\,\mu(B).$$

The event $A$ is measurable for the coordinates in $s$, the event $\sigma^{-n} B$ for the coordinates $\ge n$,
and independent coordinates generate independent σ-algebras on disjoint index sets; finally
$\mu(\sigma^{-n} B) = \mu(B)$ because [the shift preserves $\mu$](measure-preserving-shift.md).

## Sources

- O. Sarig, *Lecture Notes on Ergodic Theory* (2023), §3.3, proof of Proposition 3.5 ("any two cylinders with
  non-overlapping set of indices is independent" for Bernoulli schemes).
