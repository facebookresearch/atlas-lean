# Transition

The Lander–Green transition probability between inheritance vectors at adjacent loci with
recombination fraction `θ` and no interference: `θᵈ (1 - θ)ⁿ⁻ᵈ`, where `d = hammingDist v w` is
the number of meioses whose transmitted grandparental origin differs (Mathlib's Hamming
distance). As a function of `θ` this is the bit-flip kernel; it models recombination for
`0 ≤ θ ≤ 1/2`.
