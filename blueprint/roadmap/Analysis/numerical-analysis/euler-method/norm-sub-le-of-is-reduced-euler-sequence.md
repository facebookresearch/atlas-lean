# Initial-error propagation

Two reduced Euler sequences with the same nonnegative step
differ, after `k` steps, by at most `exp (L k h)` times their initial difference, where `L` is
the reduced Lipschitz constant. This is the one-step stability estimate
`MathlibExt.Analysis.ODE.OneStepMethod.norm_sub_le_of_lipschitzWith` on the grid `t₀ + j h`, with
no perturbation.
