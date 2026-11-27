# The per-challenge Schnorr simulator

For $q \ge 1$, the statement $y$ and the challenge $r$: draw a uniform answer $s$ and output the commitment
$g^s y^{-r}$ with the answer $s$, computed from $y$ alone. It is the [Schnorr simulator](../schnorr-identification-scheme/simulate.md)
with the challenge fixed to $r$.
