# Expurgated random coding bound, maximal error

Let $W$ be a discrete memoryless channel on finite alphabets and $p$ an input law. For every block
length $N$, every number $M \ge 1$ of code words and every $0 \le \rho \le 1$, there is a code in
which every code word has error probability under maximum-likelihood decoding (ties counted as
errors) at most

$$P_{e,m} \le 4\, M^{\rho}\, e^{-N E_0(\rho, p)}.$$

Gallager's proof: take a code with $2M$ words whose average error is at most
$(2M)^\rho e^{-N E_0}$, and keep the $M$ words with the smallest error; each has error at most twice
the average, and removing words can only lower the errors of the others. Since $2 \cdot 2^\rho \le 4$
for $\rho \le 1$, this gives the bound. Optimising over $\rho$ and $p$ at $M = e^{NR}$ gives
Gallager's $P_{e,m} \le 4 e^{-N E(R)}$, equation (23); the bound above is the fixed-$(\rho, p)$
form.

## Informally uses

- [Gallager's coding theorem](exists-code-avg-error-le.md): the code with $2M$ words.
- [Selecting the better half of a code](exists-injective-le-two-mul.md)
- [Removing code words does not increase the error](ml-error-prob-comp-le.md)

## Sources

- R. G. Gallager, "A simple derivation of the coding theorem and some applications", IEEE Trans. Inform. Theory IT-11(1):3–18, January 1965, Corollary 2, equations (23)–(25).
