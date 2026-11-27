# Gallager's coding theorem, rate form

For $N \ge 1$, $M \ge 1$ code words, the rate $R = (\ln M)/N$ in nats per channel use and every
$0 \le \rho \le 1$, there is a code whose average error probability (equiprobable messages,
maximum-likelihood decoding, ties counted as errors) is at most

$$e^{-N (E_0(\rho, p) - \rho R)}.$$

The code may depend on $\rho$. Here $M$ is any positive integer, whereas Gallager writes $M = e^{NR}$.

## Informally uses

- [Gallager's coding theorem](exists-code-avg-error-le.md): $M^\rho = e^{\rho N R}$.

## Sources

- R. G. Gallager, "A simple derivation of the coding theorem and some applications", IEEE Trans. Inform. Theory IT-11(1):3–18, January 1965, Theorem 1, equation (19).
