# The GGM construction is puncturable

Let $G(s)=(G_0(s),G_1(s))$ be a length-doubling PRG and $F(K,x)=G_{x_n}(\cdots G_{x_1}(K))$ the GGM PRF. For $x^{*}\in\{0,1\}^{n}$, let $K\{x^{*}\}$ consist of the $n$ sibling seeds $G_{1-x^{*}_i}(G_{x^{*}_{i-1}}(\cdots G_{x^{*}_1}(K)))$ for $i=1,\dots,n$. Then $K\{x^{*}\}$ determines $F(K,x)$ for every $x\ne x^{*}$, and $(K\{x^{*}\},F(K,x^{*}))\approx_c(K\{x^{*}\},U)$ with advantage at most $n$ times the PRG advantage. Hence puncturable PRFs exist if one-way functions exist.

## Proof sketch

For $x\ne x^{*}$, let $i$ be the first index with $x_i\ne x^{*}_i$; the $i$-th sibling seed is the node on $x$'s path, from which the rest of the path is computed. For security, replace the seeds along $x^{*}$'s path one level at a time by uniform strings, each step justified by PRG security; at the end $F(K,x^{*})$ is uniform and independent of the siblings.

## Depends on

- [Puncturable pseudorandom functions](puncturable-prf.md)
- [One-way function families](../../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Proof depends on

- [The GGM construction: pseudorandom generators give pseudorandom functions](../../../symmetric-key/pseudorandom-functions/the-ggm-construction-pseudorandom-generators.md)
- [Pseudorandom generators exist if and only if one-way functions exist](../../../symmetric-key/pseudorandom-generators/pseudorandom-generators-exist-if-and-only-if.md)

## Sources

- Amit Sahai, Brent Waters, "How to Use Indistinguishability Obfuscation: Deniable Encryption, and More", STOC (2014), IACR ePrint 2013/454.
- Dan Boneh, Brent Waters, "Constrained Pseudorandom Functions and Their Applications", ASIACRYPT (2013).
- Elette Boyle, Shafi Goldwasser, Ioana Ivan, "Functional Signatures and Pseudorandom Functions", PKC (2014).
