# Birkhoff's pointwise ergodic theorem

**Birkhoff's pointwise ergodic theorem** (G. D. Birkhoff, *Proof of the ergodic theorem*,
1931): for `T` preserving a finite measure `μ` and integrable `f`, the averages
`(1/n) ∑_{k<n} f ∘ T^k` converge `μ`-a.e. to `μ[f | MeasurableSpace.invariants T]`. See also
`MathlibExt.Dynamics.Ergodic.BirkhoffWanted.birkhoff_pointwise_ergodic`, the ergodic case, and
`birkhoffLimit_ae_eq_integral_of_ergodic`.
