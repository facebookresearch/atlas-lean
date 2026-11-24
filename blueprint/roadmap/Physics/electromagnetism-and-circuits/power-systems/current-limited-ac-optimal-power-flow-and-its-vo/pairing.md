# Real trace pairing of complex matrices

For a natural number $n$ and complex $n \times n$ matrices $A$ and $W$, the pairing is the real
number

$$\langle A, W \rangle = \operatorname{Re} \operatorname{tr}(A W) =
\operatorname{Re} \sum_{a, b} A_{ab}\, W_{ba}.$$

It is the real part of the Frobenius inner product $\operatorname{tr}(X^{\mathsf H} W)$ with
$X = A^{\mathsf H}$; for Hermitian $A$ it is the real part of the Frobenius inner product of $A$ and
$W$. For fixed $A$ it is [real-linear in W](is-linear-map-pairing.md). Every constraint of the
[semidefinite relaxation](sdp-feasible.md) bounds such a pairing with a Hermitian coefficient matrix
$A$.
