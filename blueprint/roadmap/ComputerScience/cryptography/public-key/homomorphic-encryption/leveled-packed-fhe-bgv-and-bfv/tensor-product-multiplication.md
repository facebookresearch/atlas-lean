# Ciphertext multiplication by tensoring

For BGV ciphertexts $\mathbf{c}=(c_0,c_1)$, $\mathbf{c}'=(c'_0,c'_1)$ of $m,m'$ with noise terms $e,e'$, the tensor $\mathbf{d}=(c_0c'_0,\;c_0c'_1+c_1c'_0,\;c_1c'_1)$ satisfies $d_0+d_1s+d_2s^{2}\equiv(m+te)(m'+te')=mm'+t(me'+m'e+te e')\pmod q$, so it is a three-component ciphertext of $mm'$ with noise of norm at most $\delta_R\|m+te\|_\infty\|m'+te'\|_\infty$, where $\delta_R=N$ is the expansion factor of $R$ ($\|ab\|_\infty\le\delta_R\|a\|_\infty\|b\|_\infty$). For BFV, the analogous tensor is scaled by $t/q$ and rounded, giving noise growth by a factor $O(\delta_Rt\|s\|_1)$ independent of the size of the input noise relative to $q$.

## Proof sketch

Expand the product of the two decryption equations. The bound uses submultiplicativity of the infinity norm in $R$ with expansion factor $N$, since each coefficient of a product is a signed sum of $N$ products of coefficients.

## Depends on

- [BGV and BFV ring ciphertexts](bgv-bfv-ciphertexts.md)

## Sources

- Zvika Brakerski, Craig Gentry, Vinod Vaikuntanathan, "(Leveled) Fully Homomorphic Encryption without Bootstrapping", ITCS (2012), IACR ePrint 2011/277.
- Junfeng Fan, Frederik Vercauteren, "Somewhat Practical Fully Homomorphic Encryption", IACR ePrint 2012/144 (2012).
