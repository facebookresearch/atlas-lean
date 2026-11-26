# The evasive LWE assumption

Let $\mathsf{Samp}$ be an efficient sampler outputting a matrix $\mathbf{P}\in\mathbb{Z}_q^{n\times m'}$ and auxiliary information $\mathsf{aux}$ (public-coin if $\mathsf{aux}$ includes the sampler's coins), let $\mathbf{B}\in\mathbb{Z}_q^{n\times m}$ be uniform, and let $\mathbf{B}^{-1}(\mathbf{P})$ denote a Gaussian preimage $\mathbf{K}$ with small entries and $\mathbf{B}\mathbf{K}=\mathbf{P}$ (sampled with a trapdoor). The *evasive LWE assumption* for $\mathsf{Samp}$ states: if

$$
(\mathbf{B},\;\mathbf{s}^{\top}\mathbf{B}+\mathbf{e}_1^{\top},\;\mathbf{s}^{\top}\mathbf{P}+\mathbf{e}_2^{\top},\;\mathsf{aux})\approx_c(\mathbf{B},\;\mathbf{c}_1^{\top},\;\mathbf{c}_2^{\top},\;\mathsf{aux})
$$

for uniform $\mathbf{s},\mathbf{c}_1,\mathbf{c}_2$ and Gaussian errors, then

$$
(\mathbf{B},\;\mathbf{s}^{\top}\mathbf{B}+\mathbf{e}_1^{\top},\;\mathbf{B}^{-1}(\mathbf{P}),\;\mathsf{aux})\approx_c(\mathbf{B},\;\mathbf{c}_1^{\top},\;\mathbf{B}^{-1}(\mathbf{P}),\;\mathsf{aux}).
$$

Intuitively, multiplying $\mathbf{s}^{\top}\mathbf{B}+\mathbf{e}_1^{\top}$ by the preimage only yields $\mathbf{s}^{\top}\mathbf{P}$ plus small noise, which is already pseudorandom, so the preimage should give no further advantage.

## Depends on

- [Learning with errors](../../hardness-assumptions/learning-with-errors.md)

## Sources

- Hoeteck Wee, "Optimal Broadcast Encryption and CP-ABE from Evasive Lattice Assumptions", EUROCRYPT (2022).
- Rotem Tsabary, "Candidate Witness Encryption from Lattice Techniques", CRYPTO (2022).
- Vinod Vaikuntanathan, Hoeteck Wee, Daniel Wichs, "Witness Encryption and Null-IO from Evasive LWE", ASIACRYPT (2022).
