# Pătraşcu's multiphase problem

Let $f : \{0,1\}^n \times \{0,1\}^n \to \{0,1\}$. In the *multiphase problem* for $f$ with parameters $k$ and $n$: in Phase I the structure receives $x_1, \dots, x_k \in \{0,1\}^n$ and may preprocess them; in Phase II it receives $y \in \{0,1\}^n$ and may update its memory with $t_u$ probes per bit of $y$; in Phase III it receives an index $i \in [k]$ and must output $f(x_i, y)$ using $t_q$ probes. Pătraşcu's original version uses set disjointness: $f(x, y) = 1$ iff the sets with characteristic vectors $x$ and $y$ intersect. Ko writes $t_{tot}$ for the probe cost of the online phases (Phases II and III) under his normalization.

## Depends on

- [Amortized update and query cost of a dynamic cell-probe structure](../dynamic-information-transfer-lower-bounds/amortized-cell-probe-costs.md)
- [Set intersection function](../../../TheoryOfComputation/communication-complexity/randomized-communication-protocols/disj-fn.md)

## Sources

- Mihai Pătraşcu, "Towards Polynomial Lower Bounds for Dynamic Problems", STOC (2010).
- Young Kun Ko, "An Omega((log n / log log n)^2) Cell-Probe Lower Bound for Dynamic Boolean Data Structures", FOCS (2026), arXiv:2603.25914.
