# Integral closure of ℤ in a field and the ring of integers of a number field

Let $K$ be a field. The ring $\mathcal{O}_K$ is the integral closure of $\mathbb{Z}$ in $K$: the subring of $K$ consisting of the elements of $K$ that are roots of a monic polynomial with integer coefficients. When $K$ is a number field, that is, a field extension of $\mathbb{Q}$ of finite degree, $\mathcal{O}_K$ is the *ring of integers* of $K$. When moreover $K$ is a subfield of $\mathbb{C}$, $\mathcal{O}_K = \mathbb{A} \cap K$ is the set of algebraic integers that lie in $K$.

## Sources

- Daniel A. Marcus, Number Fields, 2nd ed., Universitext, Springer, 2018.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for number fields as fields of characteristic zero of finite dimension over the rational numbers: `NumberField`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/NumberTheory/NumberField/Basic.lean#L40-L45.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the integral closure of the integers in a field: `NumberField.RingOfIntegers`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/NumberTheory/NumberField/Basic.lean#L92-L103.
