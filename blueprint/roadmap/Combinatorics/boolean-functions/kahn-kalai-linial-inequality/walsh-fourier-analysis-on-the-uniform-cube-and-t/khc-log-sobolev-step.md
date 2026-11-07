# Fourier-form KKL inequality given the hypercontractive bound

The KKL inequality at `p = 1/2` in Fourier form, with the hypercontractive bound as a
 hypothesis: for every Boolean `φ`, if `∑_S ρ^{2|S|} f̂(S)² ≤ ‖f‖²_{1+ρ²}` for all `ρ ∈ [0, 1]`,
 then `c · ∑_{S ≠ ∅} f̂(S)² · log (1 / maxₑ Infₑ(f)) ≤ ∑_S 4 |S| f̂(S)²`, where `f = 1_φ`. The
 hypothesis always holds (`khc_lowDegreeWeight_le`).
