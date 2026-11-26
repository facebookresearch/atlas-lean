# Correctness of Module-LWE encryption under bounded noise

In Module-LWE encryption, for an honestly generated key and ciphertext the decryption phase equals

$$
v - \mathbf{s}^{\mathsf T}\mathbf{u} = \lfloor q/2 \rceil\, m + \bigl(\mathbf{e}^{\mathsf T}\mathbf{r} - \mathbf{e}_1^{\mathsf T}\mathbf{s} + e_2\bigr).
$$

If $\|\mathbf{s}\|_\infty \le B_s$, $\|\mathbf{r}\|_\infty \le B_r$ and all error coefficients are at most $B_e$ in absolute value, every coefficient of the noise term is at most $k n (B_e B_r + B_e B_s) + B_e$ in absolute value, and whenever this bound $B$ satisfies $4B + 2 < q$, decryption returns $m$ with probability $1$.

## Proof sketch

Substitute $\mathbf{b} = \mathbf{A}\mathbf{s} + \mathbf{e}$ and $\mathbf{u} = \mathbf{A}^{\mathsf T}\mathbf{r} + \mathbf{e}_1$; the terms $\mathbf{s}^{\mathsf T}\mathbf{A}^{\mathsf T}\mathbf{r}$ cancel. A product of two polynomials in $R_q$ with coefficients bounded by $\alpha, \beta$ has coefficients bounded by $n\alpha\beta$, and rounding to the nearer of $0$ and $\lfloor q/2\rceil$ tolerates noise up to about $q/4$.

## Depends on

- [Ring-LWE and Module-LWE public-key encryption](module-lwe-encryption.md)

## Proof depends on

- [Half-modulus encoding of a bit tolerates errors below $q/4$](../lattice-trapdoors/half-modulus-bit-decoding.md)

## Sources

- Vadim Lyubashevsky, Chris Peikert and Oded Regev, "On Ideal Lattices and Learning with Errors over Rings", Advances in Cryptology – EUROCRYPT 2010, 2010.
- Roberto Avanzi et al., "CRYSTALS-Kyber: Algorithm Specifications and Supporting Documentation (version 3.02)", Third-round submission to the NIST post-quantum cryptography standardization process, dated 4 August 2021.
