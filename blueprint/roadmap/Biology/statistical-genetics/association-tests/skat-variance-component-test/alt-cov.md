# Phenotypic covariance under the variance-component alternative

For a real `n × n` matrix `V`, a real `n × m` genotype matrix `G`, real weights `w` and a real
number `τ`, the alternative covariance is `V + τ K`, where `K = G diag(w) Gᵀ` is the
[SKAT kernel](skat-kernel.md). The definition takes every real `τ` and `w`.

For `τ ≥ 0` and `w ≥ 0` it is the phenotypic covariance under the variance-component alternative:
random variant effects `β` with mean `0` and covariance `τ W`, `W = diag(w)`, independent of the
null-model terms, whose covariance is `V`, add `Cov(G β) = τ K`.
