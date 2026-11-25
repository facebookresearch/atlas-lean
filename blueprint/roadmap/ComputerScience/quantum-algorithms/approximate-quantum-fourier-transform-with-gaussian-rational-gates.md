# Approximate quantum Fourier transform with Gaussian-rational gates

This node collects an approximate quantum Fourier transform over the encoded gate model with exactly unitary
rational gates.

## Expansion

A sound expansion has separate pages for:

1. **Approximation contract.** For $n \ge 0$ and $\varepsilon > 0$, a list of $O(n^2)$ well-formed encoded 2-local gates with
   Gaussian-rational entries, generated classically in time polynomial in $n$ and $\log(1/\varepsilon)$, whose unitary $U$
   satisfies $\min_\theta \lVert U - e^{i\theta} A_{2^n} \rVert \le \varepsilon$ in operator norm, where $A_{2^n}$ is the quantum Fourier
   transform matrix (or the same bound with the accumulated phase tracked explicitly).
2. **Gates.** Each Hadamard gate is replaced by the exactly unitary gate
   $\tfrac{1+i}{2}\begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix} = e^{i\pi/4} H$, the controlled phase $R_2$ (controlled-$S$) is used
   exactly, and each controlled $R_k = \mathrm{diag}(1, 1, 1, e^{2\pi i/2^k})$ with $k \ge 3$ is replaced by an approximant of
   error at most $\varepsilon$ divided by the number of gates.
3. **Global phase.** Replacing a gate by one equal up to a global phase changes the circuit's unitary only by a
   global phase when the gate is used without control; for controlled uses the phase becomes a relative phase and
   must be accounted for, so controlled gates need their own approximation obligation.
4. **State preparation.** The uniform superposition is prepared exactly, up to a global phase, by the phase-shifted
   Hadamard gates.
5. **Small cases.** For $n = 1$ the circuit uses a clean spectator qubit to meet the two-qubit gate encoding, and the
   page states the induced operator on the data qubit; for $n = 0$ the circuit is empty.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Proof prerequisite: Gate-approximation error budget (stability of circuits and Born probabilities).

## Depends on

- [Quantum Fourier transform matrix](../../QuantumInformation/quantum-operations/quantum-fourier-transform/qft-matrix.md)
- [Encoded 2-local quantum gate](../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/qgate.md)
- [Well-formed quantum gate](../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/qgate-well-formed.md)
- [Polynomial-time computable functions](../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/is-poly-time.md)

## Proof depends on

- [Exactly unitary Gaussian-rational approximations of 1- and 2-qubit gates](../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/exactly-unitary-gaussian-rational-approximations-of-1-and-2.md)
- [Polynomial-time uniform generator of gate approximants](../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/polynomial-time-uniform-generator-of-gate-approximants.md)

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, §4.5 (exact circuit of Hadamard and controlled $R_s$ gates, at most $n^2$ gates, and the remark on omitting gates $R_s$ with large $s$). <https://arxiv.org/pdf/1907.09415v6>
- P. W. Shor, *Polynomial-time algorithms for prime factorization and discrete logarithms on a quantum computer*, arXiv:quant-ph/9508027v2 (SIAM J. Comput. 26 (1997)), Section 4 (Coppersmith's approximate Fourier transform, which ignores tiny phase factors). <https://arxiv.org/abs/quant-ph/9508027>
