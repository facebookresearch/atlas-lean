# Shor's code has distance at most three

The Pauli operator $Z_1 Z_4 Z_7 = X^0 Z^b$, with $b = e_0 + e_3 + e_6$ supported on the first qubit
of each block, has [weight](../distance-of-a-quantum-code/pauli-weight.md) three, and there is
no scalar $\lambda$ with

$$\langle \bar x | Z_1 Z_4 Z_7 | \bar y \rangle = \lambda \, \delta_{xy} \qquad (x, y \in \mathbb{F}_2)$$

for the two [Shor codewords](shor-codeword.md). So the distance condition of Preskill's
equation (7.34) fails at weight three, and the distance of Shor's code is at most three.

Proof: on a code basis state $|v\rangle$ (each block $000$ or $111$), $Z_1 Z_4 Z_7$ multiplies
the amplitude by $(-1)^{v_0 + v_3 + v_6}$, which is exactly the sign distinguishing $|\bar 1\rangle$
from $|\bar 0\rangle$. Hence $Z_1 Z_4 Z_7 |\bar 1\rangle = |\bar 0\rangle$ and
$\langle \bar 0 | Z_1 Z_4 Z_7 | \bar 1 \rangle = \langle \bar 0 | \bar 0 \rangle = 8 \ne 0$
(unnormalised codewords), while $\delta_{01} = 0$. In Preskill's equation (7.8), the same operator
$Z_1 Z_4 Z_7$ is the logical error that a misguided recovery from two phase errors produces:
it flips the encoded qubit.

## Sources

- J. Preskill, *Lecture Notes for Physics 229: Quantum Information and Computation*, Chapter 7 "Quantum Error Correction" (Caltech, 1998; https://www.preskill.caltech.edu/ph229/notes/chap7.pdf), Section 7.1, equations (7.1) and (7.8), and Section 7.3.1, equation (7.34).
