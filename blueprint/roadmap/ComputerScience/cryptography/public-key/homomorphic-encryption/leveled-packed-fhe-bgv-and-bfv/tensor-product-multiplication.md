# Ciphertext multiplication by tensoring

For BGV ciphertexts $\mathbf{c}=(c_0,c_1)$, $\mathbf{c}'=(c'_0,c'_1)$ of $m,m'$ with noise terms $e,e'$, the tensor $\mathbf{d}=(c_0c'_0,\;c_0c'_1+c_1c'_0,\;c_1c'_1)$ satisfies $d_0+d_1s+d_2s^{2}\equiv(m+te)(m'+te')=mm'+t(me'+m'e+te e')\pmod q$, so it is a three-component ciphertext of $mm'$ with noise of norm at most $\delta_R\|m+te\|_\infty\|m'+te'\|_\infty$, where $\delta_R=N$ is the expansion factor of $R$ ($\|ab\|_\infty\le\delta_R\|a\|_\infty\|b\|_\infty$). BFV multiplication $\mathrm{MultFV}$ tensors differently: it lifts the components of both ciphertexts to their centered representatives in $R$ (coefficients in $[-q/2,q/2)$), forms the degree-two product $\mathbf{c}\star\mathbf{c}'=(c_0c'_0,\;c_0c'_1+c_1c'_0,\;c_1c'_1)$ in $R[Y]$ over the integers, and only then scales each component by $t/q$, rounds coefficientwise and reduces modulo $q$, giving $\bigl([\lfloor\tfrac{t}{q}c_0c'_0\rceil]_q,[\lfloor\tfrac{t}{q}(c_0c'_1+c_1c'_0)\rceil]_q,[\lfloor\tfrac{t}{q}c_1c'_1\rceil]_q\bigr)$, which is then relinearized. The lift must precede the scaling: products of residues modulo $q$ do not determine the rounded quotient.

## Proof sketch

Expand the product of the two decryption equations. The bound uses submultiplicativity of the infinity norm in $R$ with expansion factor $N$, since each coefficient of a product is a signed sum of $N$ products of coefficients.

## Depends on

- [BGV and BFV ring ciphertexts](bgv-bfv-ciphertexts.md)

## Sources

- Zvika Brakerski, Craig Gentry, Vinod Vaikuntanathan, "(Leveled) Fully Homomorphic Encryption without Bootstrapping", ITCS (2012), IACR ePrint 2011/277.
- Jean-Claude Bajard, Julien Eynard, M. Anwar Hasan, Vincent Zucca, "A Full RNS Variant of FV Like Somewhat Homomorphic Encryption Schemes", SAC 2016, LNCS 10532 (2017), §§2–4 (`DecFV`, `MultFV`, `RelinFV`), DOI 10.1007/978-3-319-69453-5_23.
