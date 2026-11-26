# Naor's commitment is computationally hiding and statistically binding

If $G$ is a pseudorandom generator, then every efficient receiver (which may choose $R$ adversarially and keep state) guesses the committed fair bit with probability at most $\tfrac12 + \mathrm{negl}(n)$. For every $n > 0$, over an honest uniform $R$, the probability that some commitment can be opened to both $0$ and $1$ is below $2^{-n}$.

## Proof sketch

Hiding: replacing $G(s)$ by a uniform string makes both commitments uniform. Binding: a double opening requires $G(s_0) \oplus G(s_1) = R$; there are at most $2^{2n}$ such XORs among $2^{3n}$ possible $R$.

## Depends on

- [Naor's bit commitment from a pseudorandom generator](naor-bit-commitment.md)

## Sources

- M. Naor, "Bit Commitment Using Pseudorandomness", Journal of Cryptology 4(2), 1991.
