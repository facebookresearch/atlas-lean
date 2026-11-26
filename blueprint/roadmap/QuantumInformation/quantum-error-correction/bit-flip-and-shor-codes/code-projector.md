# Code space of the three-qubit bit-flip code

Index the basis states of three qubits by $v \in \mathbb{F}_2^3$. The code space of the bit-flip
code is spanned by $|000\rangle$ and $|111\rangle$, and its orthogonal projector is the diagonal
matrix

$$P = |000\rangle\langle 000| + |111\rangle\langle 111|, \qquad P_{vv} = \begin{cases} 1 & v \in \{000, 111\},\\ 0 & \text{otherwise}.\end{cases}$$

The encoding is $a|0\rangle + b|1\rangle \mapsto a|000\rangle + b|111\rangle$; each three-qubit
cluster of Shor's nine-qubit code (Preskill, equation (7.1)) uses the same pair of states in the
rotated basis $\tfrac{1}{\sqrt 2}(|000\rangle \pm |111\rangle)$.

## Sources

- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.1.
