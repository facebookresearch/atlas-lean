# The real world of the counter-mode reduction

Let `N ≠ 0`, `Y` an additive group, and the key space `K` and adversary coins
`R` finite and nonempty. For `F : K → ZMod N → Y` and every CPA adversary
against counter mode whose coins are uniform on `R` and which makes at most
`q` encryption queries, the CPA game of counter mode equals the real-world PRF
game of `F` against the reduction `ctrReduction`: with the oracle `F k`, the
reduction runs the CPA game exactly.
