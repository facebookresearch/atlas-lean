# To Bits BE

The `w`-bit big-endian encoding of `x : ZMod N`, through its canonical representative
`x.val`. It is lossless when `N ≠ 0` and `N ≤ 2 ^ w` (`ZMod.ofBitsBE_toBitsBE`,
`ZMod.toBitsBE_injective`), e.g. for serializing elements of `ℤ_N` in RSA (Katz-Lindell, 2nd ed.,
§11.5). The bound alone is not enough: for `N = 0` it holds at every width, but `ZMod 0 = ℤ` is
infinite, so no fixed width is lossless.
