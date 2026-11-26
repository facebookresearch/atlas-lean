# The heat convolution preserves the constant one

For `t > 0` and every `x`,
`heatConvolution n (fun _ => 1) t x = 1`. After the translation `y ↦ x - y`, this is the total
mass `integral_heatKernel` of the heat kernel.
