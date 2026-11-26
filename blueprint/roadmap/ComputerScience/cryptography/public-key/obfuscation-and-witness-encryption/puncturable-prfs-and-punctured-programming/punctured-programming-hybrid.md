# Punctured programming: swapping a program for a functionally equivalent punctured one

Let $\mathcal{O}$ be an indistinguishability obfuscator, $F$ a puncturable PRF, and $P_K$ a program that uses $F(K,\cdot)$. Suppose $x^{*}$ is a point at which, with overwhelming probability over the experiment's randomness, $P_K$ never evaluates $F(K,x^{*})$ (for example because $x^{*}$ is sampled outside the image of a length-doubling PRG that the program applies before calling $F$). Let $P'_{K\{x^{*}\}}$ be the program that uses $K\{x^{*}\}$ instead. Then $\mathcal{O}(P_K)\approx_c\mathcal{O}(P'_{K\{x^{*}\}})$, and in the latter experiment $F(K,x^{*})$ may be replaced by a uniform value by puncturable PRF security.

## Proof sketch

The two programs compute the same function whenever $x^{*}$ is outside the set of points where $F$ is queried, by functionality preservation; iO security applies to functionally equivalent circuits padded to the same size. The punctured key then hides $F(K,x^{*})$.

## Depends on

- [Puncturable pseudorandom functions](puncturable-prf.md)
- [Indistinguishability and virtual black-box obfuscation](../../../program-obfuscation/indistinguishability-and-virtual-black-box.md)

## Sources

- Amit Sahai, Brent Waters, "How to Use Indistinguishability Obfuscation: Deniable Encryption, and More", STOC (2014), IACR ePrint 2013/454.
