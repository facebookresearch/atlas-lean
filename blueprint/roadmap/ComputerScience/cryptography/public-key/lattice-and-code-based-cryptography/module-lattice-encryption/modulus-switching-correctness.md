# Decryption correctness after modulus switching

Let a ciphertext over $R_q$ encrypt $m$ with integer noise $\varepsilon$ (so its phase is $\lfloor q/2\rfloor m + \varepsilon$), and switch it to modulus $p$. Then the switched ciphertext has phase $\lfloor p/2 \rfloor m + \varepsilon'$ with

$$
\|\varepsilon'\|_\infty \le \tfrac{p}{q}\|\varepsilon\|_\infty + \tfrac12(1 + \|\mathbf{s}\|_1) + \Bigl|\tfrac{p}{q}\lfloor q/2 \rfloor - \lfloor p/2 \rfloor\Bigr|,
$$

and if this bound $B'$ satisfies the decoding margin $4B' + 2 < p$, decryption at modulus $p$ returns $m$; if both moduli satisfy their margins, switching preserves the decryption result.

## Proof sketch

Combine the phase bound with the noise of the source ciphertext; the extra term accounts for the different positions of the message encoding at the two moduli, so both odd and even moduli are allowed. The randomized statement is a union bound over the noise polynomials together with the centered-binomial tail bound.

## Depends on

- [Modulus switching of LWE ciphertexts](modulus-switching.md)
- [Correctness of Module-LWE encryption under bounded noise](module-lwe-encryption-correctness.md)

## Proof depends on

- [Phase error after modulus switching](modulus-switching-phase-bound.md)
- [Union bound for centered-binomial polynomial noise](centered-binomial-noise-tails.md)

## Sources

- Chris Peikert, "A Decade of Lattice Cryptography", Foundations and Trends in Theoretical Computer Science, 2016.
