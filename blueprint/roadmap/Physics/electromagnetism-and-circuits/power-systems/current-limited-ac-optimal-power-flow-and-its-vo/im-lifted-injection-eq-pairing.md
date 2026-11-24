# Imaginary part of the lifted injection as a pairing, for Hermitian W

For every natural number $n$, every complex $n \times n$ matrix $Y$, every Hermitian complex
$n \times n$ matrix $W$ and every index $k$,

$$\operatorname{Im} \sum_{j} \overline{Y_{kj}}\, W_{kj} = \langle A^Q_k, W \rangle,$$

where the left side is the imaginary part of the [lifted injection](lifted-injection.md), $A^Q_k$ is
the [reactive coefficient matrix](reactive-coeff.md) of $Y$ at $k$ and
$\langle A, W \rangle = \operatorname{Re} \operatorname{tr}(A W)$ is the [pairing](pairing.md). The
hypothesis that $W$ is Hermitian is used: it makes
$\operatorname{tr}(R_k W) = \sum_j Y_{kj} W_{jk}$, with $R_k$ keeping row $k$ of $Y$, the complex
conjugate of the lifted injection.
