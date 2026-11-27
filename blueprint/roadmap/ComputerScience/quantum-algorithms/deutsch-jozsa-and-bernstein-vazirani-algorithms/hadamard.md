# The $n$-qubit Hadamard transform

The Hadamard transform on $n$ qubits is the matrix $H_n$ indexed by $\mathbb{Z}_2^n$ with entries

$$(H_n)_{s,x} = 2^{-n/2} (-1)^{s\cdot x}, \qquad s\cdot x = \textstyle\sum_i s_i x_i \bmod 2 .$$

It maps the basis state $|x\rangle$ to $2^{-n/2} \sum_s (-1)^{s\cdot x} |s\rangle$, the change of basis
from the delta functions to the parity (character) basis of $\mathbb{Z}_2^n$. Bernstein and Vazirani
(Section 8.4, Theorem 8.4.1) build it as the tensor power of the one-qubit Hadamard gate; Cleve,
Ekert, Macchiavello and Mosca (equation (3.1)) display it without the normalisation $2^{-n/2}$.

## Background

- [Sylvester sign matrix](sylvester-sign-matrix.md): $H_n$ is $2^{-n/2}$ times this $\pm 1$ matrix, a Hadamard matrix (entries $\pm 1$, pairwise orthogonal rows).
- [Quantum Fourier transform matrix](../../../QuantumInformation/quantum-operations/quantum-fourier-transform/qft-matrix.md): the Fourier transform over $\mathbb{Z}_q$; $H_n$ is the Fourier transform over $\mathbb{Z}_2^n$.

## Sources

- E. Bernstein and U. Vazirani, "Quantum complexity theory", SIAM Journal on Computing 26 (1997), 1411–1473; author-hosted version dated September 8, 1997 (https://people.eecs.berkeley.edu/~vazirani/pubs/bv.pdf), Section 8.4. Theorem numbers on this page refer to that version.
- R. Cleve, A. Ekert, C. Macchiavello and M. Mosca, "Quantum algorithms revisited", Proceedings of the Royal Society of London A 454 (1998), 339–354; arXiv:quant-ph/9708016v1, Section 3, equations (3.1)–(3.9).
