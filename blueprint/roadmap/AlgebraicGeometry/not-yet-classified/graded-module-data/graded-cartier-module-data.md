# Graded Cartier module data

Let `p` be a prime, `B` a commutative ring and
`j : Zp2 p →+* B` a ring homomorphism, where `Zp2 p` is the ring of Witt vectors of
`GaloisField p 2`; write `σ` for the Frobenius of `WittVector p B`. The data consist of a
`WittVector p B`-module `M` with additive maps `F` and `V` satisfying `F (w • x) = σ w • F x`,
`w • V x = V (σ w • x)`, `V (w • F x) = WittVector.verschiebung w • x` and
`F (V x) = p • x`, a `WittVector p B`-linear map `ϖ` with `ϖ (V x) = V (ϖ x)`,
`ϖ (F x) = F (ϖ x)` and `ϖ (ϖ x) = p • x`, and complementary submodules `piece 0` and
`piece 1` such that `F`, `V` and `ϖ` each map one piece into the other. No field involves `j`;
it appears in `IsBaseChangeAlong`, where data over `B'` carry `φ.comp j`. The intended pieces are
the `j`-graded pieces of the Cartier module of a formal `O_D`-module, as in
`FormalODModule.toGradedCartierModuleData`.
