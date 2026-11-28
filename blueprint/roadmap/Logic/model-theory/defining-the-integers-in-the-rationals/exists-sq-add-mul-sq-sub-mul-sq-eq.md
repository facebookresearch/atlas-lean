# Rational representations by `X ^ 2 + a Y ^ 2 - p Z ^ 2`

Let `p` be an odd prime, `a` an
odd squarefree positive integer prime to `p`, and `m` a positive integer prime to `a` and to `p`,
with `m ≡ 2 (mod 4)`, or `m` odd with `(p / m) = (m / p)` (Jacobi symbols). Then
`X ^ 2 + a Y ^ 2 - p Z ^ 2 = m` has a solution in rational numbers `X, Y, Z`.

This is the case of Hasse's theorem behind the "if" halves of J. Robinson's Lemmas 3 and 4
(*J. Symbolic Logic* 14 (1949), p. 108), where `m = 2 d ^ 2 + p n ^ 2` with `a = 1`, and
`m = 2 d ^ 2 + p q n ^ 2` with `a = q`. Robinson derives these from Lemmas 1 and 2, special
cases of Hasse's theorem on rational representations by quadratic forms. Here the proof follows
the classical reduction of the four-variable Hasse–Minkowski theorem to the ternary case. Write
`m = t ^ 2 m₀` with `m₀` squarefree and take a prime `r` (Dirichlet's theorem) with
`r ≡ 1 (mod a)`, `r ≡ m₀ (mod p)`, `r ≡ p` modulo the odd part of `m₀` and `r ≡ 1 (mod 4)`, whose
class modulo `8` fixes the sign `(2 / r)`. Legendre's theorem (`Int.exists_ternary_eq_zero_iff`)
then solves `X ^ 2 + a Y ^ 2 = r` and `m₀ U ^ 2 + p V ^ 2 = r` in rationals.
