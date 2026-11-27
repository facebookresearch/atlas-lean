# Negative circular average of an extended-real function

For `u : ℂ→EReal`, `z∈ℂ` and
any real radius `r`, define `negativeCircleAverage u z r = (1/(2π)) ∫⁻_{θ∈(0,2π]} (-u(z+r
exp(iθ))).toENNReal dθ`. This is a nonnegative extended Lebesgue average using the
full-period angle measure. When `u≤0`, the encoding retains `-u`; values `u=-∞` contribute
`+∞`. The definition is total, including zero and negative radii.
