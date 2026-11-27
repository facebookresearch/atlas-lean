# Key recovery against CKKS from decryptions of honest ciphertexts

The CKKS scheme (with decryption outputting $m+e$ decoded without additional noise) is not IND-CPA-D secure: there is a polynomial-time adversary that, after one encryption query and one decryption query on the same (honestly generated) ciphertext $\mathbf{c}=(b,a)$, learns $e'=\mathrm{Dec}(\mathbf{c})-$ (the known message) up to rounding, hence the exact value $b+as\bmod q$, and solves the linear equation $as=(m+e)-b$ over $R_q$ for the secret key $s$ when $a$ is invertible (which holds with noticeable probability), or from a few such equations otherwise.

## Proof sketch

Approximate decryption returns $\mathrm{Dcd}(m+e)$, from which the adversary recovers $m+e\in R$ by re-encoding without rounding loss when parameters allow exact recovery of the integer polynomial. Knowing $m$ (its own query), it obtains $e$ and thus $b+as$ exactly in $R_q$, giving a linear system in $s$.

## Depends on

- [IND-CPA-D security for approximate homomorphic encryption](ind-cpa-d-security.md)
- [CKKS ciphertexts and approximate decryption](ckks-ciphertexts.md)

## Sources

- Baiyu Li, Daniele Micciancio, "On the Security of Homomorphic Encryption on Approximate Numbers", EUROCRYPT (2021), IACR ePrint 2020/1533.
