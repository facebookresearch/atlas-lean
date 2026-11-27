# A strongly compressing second-preimage-resistant function is one-way

Let $H$ map $n$-bit inputs to $\mathrm{out}(n)$-bit digests with $2^{\mathrm{out}(n)}/2^n$ negligible. If $H$ is second-preimage resistant, then $H$ is one-way on uniform $n$-bit inputs.

## Proof sketch

Apply the counting bound at input length $n$: an inverter with success $\varepsilon$ gives a second-preimage finder with success at least $(\varepsilon - 2^{\mathrm{out}(n) - n})/2$, and $2^{\mathrm{out}(n) - n}$ is negligible.

## Depends on

- [Second-preimage resistance](second-preimage-resistance.md)
- [One-way function families](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Proof depends on

- [Few inputs lack a second preimage, and inversion is at most twice as easy as second preimages](second-preimage-counting-and-inversion.md)

## Sources

- P. Rogaway and T. Shrimpton, "Cryptographic Hash-Function Basics: Definitions, Implications, and Separations for Preimage Resistance, Second-Preimage Resistance, and Collision Resistance", Fast Software Encryption (FSE 2004), Lecture Notes in Computer Science, Springer, 2004, pp. 371–388; Theorem 7(1) (numbering of the authors' full version).
