# Deutsch–Jozsa and Bernstein–Vazirani algorithms

Fourier sampling over $\mathbb{Z}_2^n$: apply the $n$-qubit Hadamard transform to $|0\cdots0\rangle$,
query the phase oracle $|x\rangle \mapsto (-1)^{f(x)}|x\rangle$ once, apply the Hadamard transform
again and measure. The amplitude of $|t\rangle$ is $2^{-n}\sum_x (-1)^{f(x) + t\cdot x}$. When
$f(x) = s\cdot x + b$ the outcome is $s$ with certainty (Bernstein–Vazirani), and the outcome
$0\cdots0$ separates constant from balanced functions with certainty (Deutsch–Jozsa), each with a
single query, whereas a classical algorithm needs $n$ evaluations to find $s$.

- [Balanced Boolean function](is-balanced.md)
- [Inner product of bit strings modulo two](bit-dot.md)
- [Classical evaluations: fewer than $n$ never determine $s$](exists-ne-zero-forall-bit-dot-eq-zero.md)
- [Fourier sampling state](fourier-sample.md)
- [Amplitudes of Fourier sampling](fourier-sample-apply.md)
- [Bernstein–Vazirani algorithm](fourier-sample-of-affine.md)
- [Deutsch–Jozsa algorithm, balanced case](fourier-sample-zero-of-is-balanced.md)
- [The $n$-qubit Hadamard transform](hadamard.md)
- [Normalisation of the Hadamard transform](hadamard-scale.md)
- [The Hadamard transform is self-adjoint](hadamard-conj-transpose.md)
- [The Hadamard transform is unitary](hadamard-mem-unitary-group.md)
- [The Hadamard transform is an involution](hadamard-mul-self.md)
- [The Hadamard transform is symmetric](hadamard-transpose.md)
- [The sign matrix is a Hadamard matrix](is-hadamard-sylvester-sign-matrix.md)
- [The Bernstein–Vazirani algorithm outputs $s$ with certainty](norm-sq-fourier-sample-of-affine.md)
- [Deutsch–Jozsa algorithm, constant case](norm-sq-fourier-sample-zero-of-const.md)
- [Phase oracle](phase-oracle.md)
- [Phase kickback](phase-kickback.md)
- [Sign of a bit](sign-of-bit.md)
- [Orthogonality of the parity characters](sum-sign-of-bit-bit-dot.md)
- [Sylvester sign matrix](sylvester-sign-matrix.md)

## Related topics

- [Quantum Fourier transform](../../../QuantumInformation/quantum-operations/quantum-fourier-transform/README.md): Fourier sampling over $\mathbb{Z}_q$, used by Shor's algorithm.
- [Lower bound for quantum search](../lower-bound-for-quantum-search/README.md): the other half of the query-complexity picture, where quantum speedups are limited.
