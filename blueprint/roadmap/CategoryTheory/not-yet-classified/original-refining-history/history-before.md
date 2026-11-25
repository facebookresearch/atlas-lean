# History Before

For a fixed well-founded cell tree `O`, chosen lower-set colimits `M`
and regular `chi`, the compatible section `x` over the strictly earlier
stages `Set.Iio j` determines the prefix on `before j`.

Each `i < j` contributes the prefix `priorState … i` on `after i` read off that
section, so the inputs are that section's own earlier prefixes rather than
unrelated predecessor data. Their supports `after i` are monotone; the
prefix fields are preserved along every `i ≤ k`, admit a common upper stage
below `j` for any two indices, and cover `before j`. Thus `partialLimitPrefix`
assembles them using the working-size colimits of `C`. When no stage precedes
`j`, `before j = ⊥` and the designated empty prefix is returned.
