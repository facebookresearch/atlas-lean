# To Bits BE injective

The `w`-bit encoding of `ZMod N` is injective for a nonzero modulus `N` (`[NeZero N]`) with
`N ≤ 2 ^ w`. Without `N ≠ 0` it fails: `ZMod 0 = ℤ` is infinite and has no injective fixed-width
encoding.
