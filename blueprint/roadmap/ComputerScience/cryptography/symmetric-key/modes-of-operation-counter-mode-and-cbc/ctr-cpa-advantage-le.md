# Counter mode is CPA-secure, concrete bound

Let `N ≠ 0`, `ℓ ≤ N`, and let `Y` be a finite nonempty additive group, with a
finite nonempty key space `K` and adversary coins `R`. For `F : K → ZMod N →
Y` and every adversary whose coins are uniform on `R` and which makes at most
`q` encryption queries on messages of `ℓ` blocks, the CPA advantage against
counter mode with `F` is at most the PRF advantage against `F` of the
reduction `ctrReduction` plus `q (2ℓ - 1) / (2 N)` (Katz and Lindell, Theorem
3.32).
