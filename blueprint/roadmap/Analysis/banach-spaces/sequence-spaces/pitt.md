# Pitt's theorem

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let
$1 \le q < p < \infty$. Then every bounded linear operator
$T : \ell^p(\mathbb{N}, \mathbb{K}) \to \ell^q(\mathbb{N}, \mathbb{K})$ is compact.

## Sources

- H. R. Pitt, A Note on Bilinear Forms, J. London Math. Soc. s1-11 (1936), 174–180, DOI 10.1112/JLMS/S1-11.3.174, compactness of operators `ℓ^p → ℓ^q` for `q<p`; textbook Albiac and Kalton, Topics in Banach Space Theory Prop 2.1.6; Lean states `RCLike` `lp _ p →L[𝕜] lp _ q` with `q<p<∞` compact specialization via `IsCompactOperator`.
