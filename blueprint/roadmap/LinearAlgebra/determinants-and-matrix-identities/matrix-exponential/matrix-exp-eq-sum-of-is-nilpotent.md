# Exponential of a nilpotent matrix

If $A$ is a nilpotent complex square matrix indexed by a
finite set, then there is a natural number $m$ such that
$e^A = \sum_{k=0}^{m-1} \frac{1}{k!} A^k$, where $e^A$ is the matrix exponential.

Proof: if $A^m = 0$, every term of the exponential series from index $m$ on vanishes.

## Sources

- Mathlib `docs/undergrad.yaml`, Linear algebra / Exponential / matrix exponential; R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University Press (2013), Section 3.2.
