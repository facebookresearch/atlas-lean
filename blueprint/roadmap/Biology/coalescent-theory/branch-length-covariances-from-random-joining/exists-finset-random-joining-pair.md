# Two-level Markov property of random joining

For every natural number `m` and every list `x` of natural numbers, there is a finite set `F` of
lists of block-size lists such that the
[random-joining law](../expected-site-frequency-spectrum/random-joining.md) `R_m(x, ps)` vanishes
for every `ps` outside `F`, and for all natural numbers `a ≤ b ≤ m` and all real functions `g`
and `h` on lists of natural numbers,

`∑_{ps ∈ F} R_m(x, ps) g(p_a) h(p_b) = J^a(y ↦ g(y) · (J^{b - a} h)(y))(x)`,

where `p_a` is the entry of index `a` of `ps` (the empty list if `ps` is shorter) and `J` is the
[transition operator of random joining](../expected-site-frequency-spectrum/join-step.md). So the
expectation of `g` at step `a` times `h` at step `b` of random joining started from `x` is the
[two-step expectation](join-pair.md) `P_{a,b}(g, h)(x)`.
