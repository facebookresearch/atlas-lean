# Real part of the lifted injection as a pairing, for Hermitian W

For every natural number $n$, every complex $n \times n$ matrix $Y$, every Hermitian complex
$n \times n$ matrix $W$ and every index $k$,

$$\operatorname{Re} \sum_{j} \overline{Y_{kj}}\, W_{kj} = \langle A^P_k, W \rangle,$$

where the left side is the real part of the [lifted injection](lifted-injection.md), $A^P_k$ is the
[active coefficient matrix](active-coeff.md) of $Y$ at $k$ and
$\langle A, W \rangle = \operatorname{Re} \operatorname{tr}(A W)$ is the [pairing](pairing.md). The
hypothesis that $W$ is Hermitian is used: it makes
$\operatorname{tr}(R_k W) = \sum_j Y_{kj} W_{jk}$, with $R_k$ keeping row $k$ of $Y$, the complex
conjugate of the lifted injection.
