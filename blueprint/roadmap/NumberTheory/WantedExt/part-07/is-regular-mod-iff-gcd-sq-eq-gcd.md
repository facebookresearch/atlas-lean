---
declaration: theorem
origin: cited
statement: formalized
lean: isRegularMod_iff_gcd_sq_eq_gcd
---

# Regular Residues Wanted

Morgado's characterization of regular integers modulo `n`: for
`0 < n` and `m : ℤ`, the congruence `m^2 x ≡ m (mod n)` is solvable
in `ℤ` iff `gcd(m^2, n) = gcd(m, n)` iff `gcd(m, n)` is a unitary
divisor of `n`, i.e. `Nat.Coprime (Nat.gcd m.natAbs n)
(n / Nat.gcd m.natAbs n)`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.RegularResiduesWanted](../../../../sources/v2/WantedExt.md)
- Klaus Dohmen and Mandy Lange-Geisler, "On the Number of Regular Integers Modulo `n` and Its Significance for Cryptography", Journal of Integer Sequences 29 (2026), Article 26.2.4, Proposition [Morgado 1972] (label `sec:regul-numb-unit-2`): <https://cs.uwaterloo.ca/journals/JIS/VOL29/Dohmen/dohmen4.tex>.
