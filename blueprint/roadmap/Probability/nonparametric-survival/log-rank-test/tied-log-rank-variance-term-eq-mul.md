# Tied Log Rank Variance Term eq mul

Algebraic identity: for `1 < Y` and any naturals `Y₁`, `d`, the term equals
`d · (Y₁ (Y - Y₁) / Y²) · ((Y - d) / (Y - 1))`, with all subtractions in `ℝ`. Only on the domain
`Y₁ ≤ Y`, `d ≤ Y` do the factors read as the Breslow contribution of the `d` tied events and the
finite-population correction (see `tiedLogRankVarianceTerm_one`, `tiedLogRankVarianceTerm_le`);
outside it the factors can be negative.
