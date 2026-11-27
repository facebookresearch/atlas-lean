# Bit-flip and Shor codes

The three-qubit bit-flip code encodes one qubit as $a|0\rangle + b|1\rangle \mapsto a|000\rangle + b|111\rangle$. A single bit flip moves the code space to an orthogonal subspace, which the two-qubit parities $Z_1 Z_2$ and $Z_2 Z_3$ identify without disturbing the encoded state; the flipped qubit is then flipped back. The code does not protect against phase errors. Shor's nine-qubit code repeats a three-qubit cat state $\tfrac{1}{\sqrt 2}(|000\rangle \pm |111\rangle)$ three times, so that the inner blocks correct bit flips and the outer repetition corrects phase flips; it corrects an arbitrary error on any one qubit (Preskill, Section 7.1).

The bit-flip code corrects the identity and the three single bit flips, as the Knill–Laflamme conditions show. Shor's code has distance at most three, and in fact exactly three.

- [Code space of the three-qubit bit-flip code](code-projector.md)
- [The code projector is an orthogonal projector](code-projector-is-proj.md)
- [Single bit flips on three qubits](single-flip.md)
- [Knill–Laflamme conditions for the bit-flip code](knill-laflamme-bit-flip.md)
- [The three-qubit bit-flip code corrects any single bit flip](is-correctable-bit-flip.md)
- [Codewords of Shor's nine-qubit code](shor-codeword.md)
- [Shor's code has distance at most three](shor-code-distance-at-most-three.md)
- [Shor's code has distance three](shor-codeword-distance-three.md)

## Related topics

- [Knill–Laflamme conditions](../knill-laflamme-conditions/README.md): the criterion through which the bit-flip code is shown to correct single bit flips.
- [CSS codes](../css-codes/README.md): the Pauli operators $X^a Z^b$ used for the bit flips are defined there.
- [Distance of a quantum code](../distance-of-a-quantum-code/README.md): the bit-flip code has distance $1$ for general Pauli errors, since a single phase flip $Z_1$ acts on the code as a logical operator; it is designed for the restricted error set of bit flips.

## Sources

- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.1, equations (7.1)–(7.2).
- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 3.1.
