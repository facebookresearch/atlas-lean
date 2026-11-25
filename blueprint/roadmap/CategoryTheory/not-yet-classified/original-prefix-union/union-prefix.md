# Union Prefix

For a fixed cell tree `O`, chosen lower-set colimits `M`, regular `chi`
and working-size colimits in `C`, assemble a prefix on `B` from a coherent
family of prefixes on a monotone family of lower sets covering `B`.

The inputs are `S : I → LowerSet P`, monotone with `S i ≤ B`; a prefix `F i`
on each `S i`; `Preserves` of the actual prefix fields from `F i` to `F j`
for every `i ≤ j`; a common upper stage for each pair `i`, `j`;
and, for every `p : B`, some `i` with `p ∈ S i`. If `I` is empty that cover
forces `B = ⊥`, and the designated empty prefix is returned; otherwise the
assembly is `partialLimitPrefix`, which retains every `F i`
(`unionPrefix_preserves`). The family is a cover by lower sets of `B`, not an
arbitrary one; the `F i` are prefixes of the same goodification data, not
independent ones; and directedness is the pairwise upper stage required
here.
