# Pooled Gamma–Poisson conjugacy

With prior `λ ~ Gamma(a, b)` (`a, b > 0`) and
conditionally independent cell counts `kⱼ ~ Po(sⱼ λ)` (`sⱼ > 0`), the posterior density (joint
likelihood times prior density over the joint marginal likelihood) is the
`Gamma(a + ∑ⱼ kⱼ, b + ∑ⱼ sⱼ)` density. With no cells it is the prior.
