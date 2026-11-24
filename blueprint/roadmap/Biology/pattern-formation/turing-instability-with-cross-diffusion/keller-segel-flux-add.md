# Linearization of the chemotactic flux

At state `s + p` the flux is the linear map
`kellerSegelDiffusion d_u d_v χ (s 0)` applied to the gradient, plus the remainder
`(-χ p₀ v_x, 0)`, which is bilinear in the perturbation `p` and the gradient `g`. So the
linearized system at a homogeneous state `s` has diffusion matrix
`kellerSegelDiffusion d_u d_v χ (s 0)`.
