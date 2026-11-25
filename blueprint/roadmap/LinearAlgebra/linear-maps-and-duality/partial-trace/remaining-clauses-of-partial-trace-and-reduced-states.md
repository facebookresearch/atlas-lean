# Characterization of the partial trace by the product rule

The partial traces over each factor, their rank-one formulas, their preservation of positive semidefiniteness and of
the trace (so that a reduced state $\mathrm{Tr}_Y \rho$ of a density operator is a density operator), and their
adjointness to amplification by the identity (so that a measurement on $X$ has the same outcome probabilities on
$\rho$ and on $\mathrm{Tr}_Y \rho$) are separate pages, including those listed under the dependencies. The product rule
$\mathrm{Tr}_Y(A \otimes B) = \mathrm{Tr}(B)\, A$, hence $\mathrm{Tr}_Y(\rho \otimes \sigma) = \rho$ for density operators, is a
separate result. This node collects only the characterization those results do not state.

## Expansion

A sound expansion has a page for:

1. **Characterization.** $\mathrm{Tr}_Y$ is the unique linear map $L(X \otimes Y) \to L(X)$ with
   $\mathrm{Tr}_Y(A \otimes B) = \mathrm{Tr}(B)\, A$ for all $A$ and $B$, and likewise for the partial trace over the first
   factor.

## Depends on

- [Partial trace over the second factor](partial-trace-right.md)
- [Partial trace over the first factor](partial-trace-left.md)

## Related topics

- [Right partial trace preserves positive semidefiniteness](pos-semidef-partial-trace-right.md)
- [Right partial trace of a density matrix has trace one](trace-partial-trace-right-of-trace-eq-on.md)
- [Right partial trace is adjoint to identity amplification](trace-partial-trace-right-mul.md)

## Sources

- J. Watrous, *The Theory of Quantum Information*, Cambridge University Press, 2018 (author copy), Section 2.1.3, equations (2.32) and (2.33) (the partial trace is the unique linear map with $\mathrm{Tr}_{Y_k}(Y_1 \otimes \cdots \otimes Y_n) = \mathrm{Tr}(Y_k)\, Y_1 \otimes \cdots$ with the factor $Y_k$ omitted). <https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf>
- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, §18.3 (reduced density matrices). <https://arxiv.org/pdf/1907.09415v6>
