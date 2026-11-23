# Condition numbers of sign matrices

For a positive integer $n$, the minimum condition number $\kappa_n$ of order $n$ is the least condition number of a real $n \times n$ sign matrix, a matrix all of whose entries are $1$ or $-1$; the minimum is taken over the finitely many such matrices. Here the condition number of a real square matrix with singular values $\sigma_0 \ge \dots \ge \sigma_{n-1}$ is $\sigma_0 / \sigma_{n-1}$, and $\infty$ when $\sigma_{n-1} = 0$.

## Idea

A matrix with condition number $1$ is a multiple of an orthogonal matrix, and a sign matrix of that kind is exactly a Hadamard matrix. So $\kappa_n = 1$ for orders $n$ where a Hadamard matrix exists, which the Hadamard conjecture predicts for all multiples of $4$, and the question is how close to $1$ the condition number of a sign matrix can be in the other orders. Adding the identity to a symmetric conference matrix gives a sign matrix with small condition number. The decay exponent records the rate: it is the supremum of the exponents $\alpha$ for which $\kappa_n = 1 + f(n)/n^\alpha$ with $f$ growing more slowly than every power of $n$.

## Statements

- [Minimum condition number of sign matrices](minimum-condition-number.md)
- [Condition number of a square real matrix](condition-number.md): the condition number of a real square matrix
- [Condition number as a singular-value ratio](condition-number-eq-ratio-of-smallest-ne.md): the ratio of extreme singular values when the smallest is nonzero
- [Infinite condition number from a vanishing singular value](condition-number-eq-top-of-smallest-eq-z.md): infinite when the smallest singular value vanishes
- [The zero matrix has infinite condition number](condition-number-zero.md): the zero matrix
- [Condition number of the order-one identity](condition-number-one-order-one.md): the order-one identity
- [Condition numbers are at least one](one-le-condition-number.md): condition numbers are at least $1$
- [Boolean encoding of sign matrices](sign-matrix.md): sign matrices encoded by Boolean matrices
- [Real sign matrix of a Boolean matrix](realize.md): the real sign matrix of a Boolean matrix
- [Realized sign matrices have entries $\pm 1$](realize-entries.md): its entries are $\pm 1$
- [Boolean matrices realize exactly the sign matrices](exists-realize-iff.md): Boolean matrices give exactly the sign matrices
- [The minimum condition number is attained](minimum-condition-number-attained.md): the minimum is attained
- [The minimum condition number is at least one](one-le-minimum-condition-number.md): $\kappa_n \ge 1$
- [Minimum condition number of order one](minimum-condition-number-one.md): $\kappa_1 = 1$
- [Subpolynomial sequences](is-subpolynomial.md): subpolynomial sequences
- [Admissible decay exponents](is-admissible-exponent.md): admissible exponents
- [Decay exponent of minimum sign-matrix condition numbers](decay-exponent.md): the decay exponent, the open quantity
- [Hadamard hypothesis](hadamard-hypothesis.md): the Hadamard conjecture, as a hypothesis
- [Symmetric conference matrices](is-symmetric-conference.md): symmetric conference matrices
- [Adding the identity to a symmetric conference matrix gives a sign matrix](exists-realize-add-one.md): a conference matrix plus the identity is a sign matrix
