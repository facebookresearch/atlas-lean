# Pseudorandom generators exist if and only if one-way functions exist

In the uniform probabilistic polynomial-time adversary model, there is a pseudorandom generator (a polynomial-time computable $G : \{0,1\}^n \to \{0,1\}^{\ell(n)}$ with $\ell(n) > n$ whose output on a uniform seed is computationally indistinguishable from uniform) if and only if there is a one-way function. Every pseudorandom generator is a one-way function; the converse, due to Håstad, Impagliazzo, Levin and Luby, constructs a pseudorandom generator from any one-way function through pseudoentropy generators and universal hashing.

## Depends on

- [One-way function families](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)
- [PRG advantage](prg-advantage.md)
- [Computational pseudoentropy](computational-pseudoentropy.md)

## Sources

- J. Håstad, R. Impagliazzo, L. A. Levin and M. Luby, "A pseudorandom generator from any one-way function", *SIAM Journal on Computing* 28(4):1364–1396, 1999
