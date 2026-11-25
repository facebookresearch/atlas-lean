# Correctness of Goldwasser–Micali encryption of one bit

For a [valid key](is-key.md) $(y, p, q)$ for the modulus $N$, every bit $b$ and every unit $x$ modulo
$N$, [trapdoor decryption](decrypt-bit.md) with $p$ and $q$ of the [encryption](encrypt-bit.md) of $b$
under $y$ with randomness $x$ returns $b$.

## Informally uses

- [Goldwasser–Micali's Lemma 2](is-square-iff-euler.md)
- [Residuosity reveals the bit](is-square-encrypt-bit-iff.md)

## Sources

- S. Goldwasser and S. Micali, "Probabilistic encryption & how to play mental poker keeping secret all partial information", Proc. 14th ACM STOC (1982), 365-377, Section 4.
