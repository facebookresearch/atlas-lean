# Quantum query algorithms with phase and value oracles

A $T$-query *quantum query algorithm* on inputs $x \in \Sigma^N$ acts on a finite-dimensional space $\mathbb{C}^{[N] \times V \times W}$ (query register, value register, workspace) by alternating fixed unitaries (or linear isometries) $U_0, \dots, U_T$ with $T$ applications of the oracle $O_x$. For Boolean inputs the *phase oracle* is $O_x|i, b, w\rangle = (-1)^{b x_i}|i, b, w\rangle$, equivalent up to Hadamard gates to the bit oracle $|i, b\rangle \mapsto |i, b \oplus x_i\rangle$; for a general alphabet $\Sigma$ the *value oracle* applies, on the value register, a unitary $\mathrm{step}(x_i)$ chosen from a fixed family indexed by $\Sigma$. The output is obtained by measuring the final state $U_T O_x \cdots O_x U_0 |\psi_0\rangle$ with a fixed projective measurement; the algorithm computes $f$ with error $\varepsilon$ if the correct value is obtained with probability at least $1 - \varepsilon$ on every input. $Q_\varepsilon(f)$ is the least such $T$.

## Sources

- R. Beals, H. Buhrman, R. Cleve, M. Mosca and R. de Wolf, "Quantum Lower Bounds by Polynomials", Journal of the ACM 48(4), 2001.
- A. Ambainis, "Quantum Lower Bounds by Quantum Arguments", Journal of Computer and System Sciences 64(4), 2002.
- R. de Wolf, "Quantum Computing: Lecture Notes", arXiv:1907.09415, 2019.
