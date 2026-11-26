# Heat convolution

For `g : EuclideanSpace ℝ (Fin n) → ℝ` and a time `t`,
`heatConvolution n g t x = ∫ y, g y * heatKernel (EuclideanSpace ℝ (Fin n)) t (x - y)`, the
convolution of `g` with the heat kernel at time `t`. The definition accepts any `g`: where
`y ↦ g y * heatKernel _ t (x - y)` is not integrable, the Bochner integral is `0`. The results of
this file take bounded data: `heat_convolution_smooth` and
`heat_convolution_satisfies_heat_equation` assume `g` a.e. strongly measurable with `|g y| ≤ M`
for almost every `y`, and the generator results take compactly supported `C²` data. It is meant
for `t > 0`: for `n > 0` the kernel vanishes at `t = 0` (`0 ^ (-n / 2) = 0`), so
`heatConvolution n g 0 = 0` for every `g`, the constant `1` included.
