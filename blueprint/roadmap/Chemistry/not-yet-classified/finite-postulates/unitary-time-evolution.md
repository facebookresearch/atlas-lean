# Unitary time evolution

For a Hermitian Hamiltonian `H`, real time `t`, and real
`ħ ≠ 0`, the propagator `exp (-(t / ħ) • (I • H))`, i.e. `exp (-i H t / ħ)`, is unitary. The
exponent is skew-Hermitian, and Mathlib's `NormedSpace.exp_mem_unitary_of_mem_skewAdjoint`
applies; the norm used is the `L²` operator norm on matrices, under which `Matrix n n ℂ` is a
complete normed ring with continuous `star`, with the `ℚ`-algebra structure restricted from `ℂ`.
The hypothesis `ħ ≠ 0` belongs to the physical statement; the proof does not use it.
