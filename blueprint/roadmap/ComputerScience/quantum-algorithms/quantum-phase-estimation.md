# Quantum phase estimation

Let $U$ be a unitary with an eigenvector $|u\rangle$, $U|u\rangle = e^{2\pi i\varphi}|u\rangle$ with
$\varphi \in [0,1)$, and suppose controlled-$U^{2^j}$ gates are available for $j = 0, \dots, n-1$. The
phase-estimation circuit on $n$ control qubits (Hadamard gates, the controlled powers of $U$, then the inverse
quantum Fourier transform and a measurement) outputs $b = 2^n\varphi$ with certainty when $2^n\varphi$ is an integer.
Otherwise, with probability at least $4/\pi^2$, it outputs an integer $b \in \{0, \dots, 2^n - 1\}$ such that
$b/2^n$ is a nearest $n$-bit approximation of $\varphi$ modulo $1$, that is, $b/2^n$ minimizes the distance to
$\varphi$ on the circle $\mathbb{R}/\mathbb{Z}$.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Statement prerequisite: Quantum query (oracle) model.
- Proof prerequisite: The phase-estimation probability bound $|\sum_{k<2^n} e^{2\pi i k\delta}|^2/4^n \ge 4/\pi^2$ for $|\delta| \le 2^{-n-1}$.

## Proof depends on

- [Quantum Fourier transform matrix](../../QuantumInformation/quantum-operations/quantum-fourier-transform/qft-matrix.md)

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, §4.6. <https://arxiv.org/pdf/1907.09415v6>
- R. Cleve, A. Ekert, C. Macchiavello and M. Mosca, *Quantum algorithms revisited*, Proc. R. Soc. Lond. A 454 (1998) 339–354; arXiv:quant-ph/9708016, §5 (best $m$-bit approximation with probability at least $4/\pi^2$). <https://arxiv.org/abs/quant-ph/9708016>
