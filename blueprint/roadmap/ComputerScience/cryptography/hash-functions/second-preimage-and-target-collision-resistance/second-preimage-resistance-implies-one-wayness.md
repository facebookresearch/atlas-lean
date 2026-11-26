# A strongly compressing second-preimage-resistant function is one-way

Let $H$ map $n$-bit inputs to $\mathrm{out}(n)$-bit digests with $2^{\mathrm{out}(n)}/2^n$ negligible. If $H$ is second-preimage resistant, then $H$ is one-way on uniform $n$-bit inputs.

## Proof sketch

Apply the counting bound with $s = 2^{n - \mathrm{out}(n)}$: an inverter with success $\varepsilon$ gives a second-preimage finder with success at least $(\varepsilon - 1/s)/2$, and $1/s$ is negligible.

## Depends on

- [Second-preimage resistance](second-preimage-resistance.md)
- [One-way function families](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Proof depends on

- [Few inputs lack a second preimage, and inversion is at most twice as easy as second preimages](second-preimage-counting-and-inversion.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
