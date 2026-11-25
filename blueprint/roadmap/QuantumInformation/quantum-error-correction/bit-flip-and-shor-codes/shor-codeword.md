# Codewords of Shor's nine-qubit code

Shor's code encodes one qubit into nine. Its basis codewords repeat a three-qubit cat state three
times (Preskill, equation (7.1)):

$$|\bar 0\rangle = \Big[\tfrac{1}{\sqrt 2}(|000\rangle + |111\rangle)\Big]^{\otimes 3}, \qquad
|\bar 1\rangle = \Big[\tfrac{1}{\sqrt 2}(|000\rangle - |111\rangle)\Big]^{\otimes 3}.$$

Here they are taken without the factor $2^{-3/2}$, as functions on the basis
$\mathbb{F}_2^9$: for $x \in \mathbb{F}_2$, the amplitude of $|v\rangle$ in $|\bar x\rangle$ is $0$
unless each block $v_0 v_1 v_2$, $v_3 v_4 v_5$, $v_6 v_7 v_8$ is $000$ or $111$, and is then
$(-1)^{x m}$, where $m \equiv v_0 + v_3 + v_6 \pmod 2$ counts the blocks equal to $111$. Both
codewords have squared norm $8$.

Each block is a codeword of the [bit-flip code](code-projector.md) written in the rotated basis,
which is why the inner blocks detect bit flips (parities $Z_1 Z_2$, $Z_2 Z_3$, …) and the outer
repetition detects phase flips (parities $X_1 \cdots X_6$, $X_4 \cdots X_9$).

## Sources

- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.1, equations (7.1)–(7.5).
