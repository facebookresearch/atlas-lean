# Puncturable pseudorandom functions

A *puncturable PRF* is a PRF $F:\mathcal{K}\times\{0,1\}^{n}\to\{0,1\}^{m}$ with algorithms $\mathsf{Puncture}(K,x^{*})\to K\{x^{*}\}$ and $\mathsf{Eval}(K\{x^{*}\},x)$ such that (functionality preservation) $\mathsf{Eval}(K\{x^{*}\},x)=F(K,x)$ for all $x\ne x^{*}$, and (selective pseudorandomness at the punctured point) for every efficient adversary that chooses $x^{*}$ before seeing anything, $(K\{x^{*}\},F(K,x^{*}))\approx_c(K\{x^{*}\},U_m)$. Puncturing at sets $S$ is defined analogously.

## Depends on

- [Asymptotic PRF security relative to a class of distinguishers](../../../symmetric-key/pseudorandom-functions/prfsecure.md)

## Sources

- Amit Sahai, Brent Waters, "How to Use Indistinguishability Obfuscation: Deniable Encryption, and More", STOC (2014), IACR ePrint 2013/454.
- Dan Boneh, Brent Waters, "Constrained Pseudorandom Functions and Their Applications", ASIACRYPT (2013).
- Elette Boyle, Shafi Goldwasser, Ioana Ivan, "Functional Signatures and Pseudorandom Functions", PKC (2014).
- Aggelos Kiayias, Stavros Papadopoulos, Nikos Triandopoulos, Thomas Zacharias, "Delegatable Pseudorandom Functions and Applications", CCS (2013).
