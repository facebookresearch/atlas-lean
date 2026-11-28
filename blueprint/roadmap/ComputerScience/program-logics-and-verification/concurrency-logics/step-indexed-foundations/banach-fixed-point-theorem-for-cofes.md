# Banach fixed-point theorem for complete OFEs

Every contractive map on an inhabited complete OFE has exactly one fixed point. This step-indexed form of Banach's theorem gives meaning to the guarded recursive definitions of Iris.

**Theorem.** Let $T$ be an inhabited COFE and $f : T \to T$ contractive. Then there is a unique $\mathrm{fix}_T f \in T$ with $f(\mathrm{fix}_T f) = \mathrm{fix}_T f$.

Counterpart: Mathlib states Banach's fixed-point theorem for a nonempty complete metric space as `ContractingWith.fixedPoint` with uniqueness `ContractingWith.fixedPoint_unique`, and for a complete extended metric space as `ContractingWith.efixedPoint`, which needs a starting point $x$ with $\mathrm{edist}\,x\,(f\,x) \neq \infty$ (all in `Mathlib/Topology/MetricSpace/Contracting.lean`); the statement here is the COFE form used by the source, not a new result.

## Depends on

- [Complete ordered families of equivalences](complete-ordered-families-of-equivalences.md)
- [Non-expansive and contractive maps](non-expansive-and-contractive-maps.md)

## Proof depends on

- [Complete ordered families of equivalences](complete-ordered-families-of-equivalences.md)
- [Non-expansive and contractive maps](non-expansive-and-contractive-maps.md)
- [Ordered families of equivalences](ordered-families-of-equivalences.md)

## Expansion

The source states the theorem without proof. A standard argument: from any $x_0$, the iterates $f^{k+1}(x_0)$ form a chain because $f$ is contractive; the limit is a fixed point because $f$ is non-expansive; and two fixed points are $n$-equal for every $n$ by induction on $n$ using contractiveness, hence equal.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 5.6, Theorem 4 (Banach's fixed point), and Section 8.1 (only the uniform-predicate type and function spaces into it must be complete).
