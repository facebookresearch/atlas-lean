# Empirical risk minimizer

For a loss `L h z`, a class `C` and a nonempty sample `S`, the
predictor `h` is an empirical risk minimizer over `C` on `S` if `h ∈ C` and no member of `C` has
smaller empirical risk on `S` (Shalev-Shwartz and Ben-David, *Understanding Machine Learning*,
2014, Section 2.3: `ERM_H(S) ∈ argmin_{h ∈ H} L_S(h)`). Ties are allowed, so a sample can have
several minimizers; over an empty class there is none.
