# Shor's code has distance three

Two statements together. First, for every Pauli operator $X^a Z^b$ on nine qubits of
[weight](../distance-of-a-quantum-code/pauli-weight.md) at most $2$ there is a scalar
$\lambda$ such that, for the two [Shor codewords](shor-codeword.md) $|\bar x\rangle$,
$|\bar y\rangle$ ($x, y \in \mathbb{F}_2$),

$$\langle \bar x | X^a Z^b | \bar y \rangle = \lambda \, \delta_{xy}.$$

Second, some Pauli operator of weight three violates this. Preskill defines the distance as the
minimum weight of a violating Pauli operator (equation (7.34)), so together they say that Shor's
code is a $[[9, 1, 3]]$ code; Gottesman checks it through the stabilizer ("The distance of this code
is in fact three"). The second statement is
[Shor's code has distance at most three](shor-code-distance-at-most-three.md), with the witness
$Z_1 Z_4 Z_7$.

Because the two unnormalised codewords have the same norm, the condition is the same as for the
normalised ones, and the first statement is the basis form of
[distance at least $3$](../distance-of-a-quantum-code/has-distance-at-least.md) for the projector
onto their span. With the theorem that
[a code of distance $2t + 1$ corrects $t$ errors](../distance-of-a-quantum-code/is-correctable-of-has-distance-at-least.md),
it gives Preskill's statement that "a single error acting on any one of the nine qubits in the block
will cause no irrevocable damage".

Gottesman's argument for the first statement: every operator of weight one or two anticommutes with
some element of the stabilizer, so that both sides vanish, except $Z_a Z_b$ with $a, b$ in the same
block, which lies in the stabilizer and acts as the identity on the code. Besides $Z_1 Z_4 Z_7$,
the operator $X_1 X_2 X_3$ also violates the condition at weight three: it maps $|\bar 0\rangle$ to
$|\bar 0\rangle$ and $|\bar 1\rangle$ to $-|\bar 1\rangle$ (Preskill, equation (7.7)).

## Background

- [Distance of a quantum code (lower bound)](../distance-of-a-quantum-code/has-distance-at-least.md): the projector form of the first statement.
- [Dimension of a stabilizer code](../stabilizer-codes/finrank-stabilizer-code.md): Shor's code is the stabilizer code of eight generators on nine qubits, of dimension $2^{9-8} = 2$.

## Sources

- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.1, equations (7.1), (7.7) and (7.8), and Section 7.3.1, equation (7.34).
- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 3.1.
