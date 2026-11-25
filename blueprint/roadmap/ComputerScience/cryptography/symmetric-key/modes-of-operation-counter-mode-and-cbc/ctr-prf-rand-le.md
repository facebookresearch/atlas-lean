# Counter-mode reduction against a random function

Let `N ≠ 0`, `ℓ ≤ N`, and let `Y` be a finite nonempty additive group, with a
finite nonempty key space `K` and adversary coins `R`. For every adversary
`Adv` and `q : ℕ`, when the reduction `ctrReduction Adv q` is given a truly
random function, its success probability differs from `1/2` by at most `q (2ℓ
- 1) / (2 N)`; it is exactly `1/2` unless the challenge counter range overlaps
the counter range of one of the at most `q` encryption queries.
