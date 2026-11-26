# A one-way function need not be second-preimage resistant

Let $h$ be one-way on $n$-bit inputs and fix a bit $b$. Then $h'(x) = h(x_1 \cdots x_{n-1} b)$ (the last input bit is overwritten by $b$) is one-way: an inverter for $h'$ with success $\varepsilon$ yields an inverter for $h$ with success at least $\varepsilon/2$. But $h'$ is not second-preimage resistant: flipping the last bit of the challenge gives a different input with the same image, with probability $1$.

## Proof sketch

Given $y = h(x)$ for uniform $x$, run the inverter for $h'$ on $y$ and overwrite the last bit of its answer by $b$. With probability $1/2$ the challenge $x$ ends in $b$, and then $y$ is distributed exactly as $h'$ of a uniform input.

## Depends on

- [Second-preimage resistance](second-preimage-resistance.md)
- [One-way function families](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)

## Sources

- P. Rogaway and T. Shrimpton, "Cryptographic Hash-Function Basics: Definitions, Implications, and Separations for Preimage Resistance, Second-Preimage Resistance, and Collision Resistance", Fast Software Encryption (FSE 2004), Lecture Notes in Computer Science, Springer, 2004, pp. 371–388; Theorem 15(3), construction $H_3$ of Figure 3 (numbering of the authors' full version).
