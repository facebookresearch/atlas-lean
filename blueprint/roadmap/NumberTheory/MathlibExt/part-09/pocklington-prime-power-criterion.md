---
article_id: af_b6599247a5fd448b9c9206ae
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.pocklington_prime_power_criterion
---

# Pocklington Prime Power Criterion

Pocklington N-1 primality criterion for prime powers (Pocklington, 1914),
as stated in Grau and Oller-Marcen, "A primality test for Kp^n+1 numbers",
arXiv:1011.4836v3, lines 60-69. Let `N = K * p ^ e + 1` with `p` prime,
`0 < K`, and `K < p ^ e`. If some `a` satisfies `a ^ (N - 1) ≡ 1 (mod N)` and
`gcd (a ^ ((N - 1) / p) - 1, N) = 1`, then `N` is prime. Lines 60-69 give the
complete condition, including `gcd(a^((N-1)/p)-1,N)=1`. The source's integer
witness `a ∈ ℤ` is represented here by a natural residue representative
`a : ℕ`, using `Nat.ModEq` and `Nat.gcd` with natural subtraction in the
exponents.

Proof: The proof follows Pocklington's standard least-prime-factor order argument, from
Pocklington (1914) as stated by Grau and Oller-Marcen, arXiv:1011.4836v3, lines 60-69.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PocklingtonPrimePowerCriterion](../../../../sources/v2/MathlibExt.md)
