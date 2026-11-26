# Real trace pairing of complex matrices

For a natural number $n$ and complex $n \times n$ matrices $A$ and $W$, the pairing is the real
number

$$\langle A, W \rangle = \operatorname{Re} \operatorname{tr}(A W) =
\operatorname{Re} \sum_{a, b} A_{ab}\, W_{ba}.$$

For fixed $A$ it is [real-linear in W](is-linear-map-pairing.md). Every constraint of the
[semidefinite relaxation](sdp-feasible.md) other than positive semidefiniteness bounds such a
pairing of $W$ with a coefficient matrix, shifted by a demand in the power constraints.
