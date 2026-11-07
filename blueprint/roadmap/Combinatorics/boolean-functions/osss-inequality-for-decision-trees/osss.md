# OSSS inequality

**OSSS inequality**, covariance form (O'Donnell, Saks, Schramm, Servedio, *Every decision tree
 has an influential variable*, FOCS 2005; in this form Duminil-Copin, Raoufi, Tassion, Ann. of
 Math. 2019): if the decision tree `T` computes the Boolean function `f`, then for every real
 function `g` and every product probability measure, `Cov(f, g) ≤ ∑ᵢ δᵢ(T) Infᵢ(g)`, where
 `Infᵢ(g) = 𝔼 |g(ω^{i ↦ 1}) - g(ω^{i ↦ 0})|`.

This is `osss_cov` with the weight and its hypothesis as leading arguments.
