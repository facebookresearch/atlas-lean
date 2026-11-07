# Scottish Book Problem 74: the coefficient bound holds

Let $n \ge 1$, let $a_k$ be real
coefficients indexed by multi-indices $k = (k_1, \dots, k_n) \in \mathbb{N}^n$, and let
$P(t) = \sum_{k_1 + \cdots + k_n = n} a_k \, t_1^{k_1} \cdots t_n^{k_n}$ be the corresponding
homogeneous polynomial of degree $n$ on $\mathbb{R}^n$. If $|P(t)| \le 1$ for every
$t \in \mathbb{R}^n$ with $|t_1| + \cdots + |t_n| \le 1$, then
$|a_k| \le n^n / (k_1! \cdots k_n!)$ for every $k \in \mathbb{N}^n$ with
$k_1 + \cdots + k_n = n$.

## Sources

- S. Mazur and W. Orlicz, Problem 74 of the Scottish Book; typescript PDF p.36, printed p.33; see the commentary in R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015). Proved by the classical polarization identity; the Rademacher form is Lemma 12 of M. Chatzakou and Y. Sarantopoulos, "Estimates for polynomial norms on Banach spaces", arXiv:2107.05993. Sketch: let `P` be `n`-homogeneous with `|P(t)| ≤ 1` for `‖t‖₁ ≤ 1`, and let `L` be its symmetric `n`-linear polar form. Polarization gives `L(x₁, …, xₙ) = (1/(2ⁿ n!)) Σ_{ε ∈ {±1}ⁿ} ε₁⋯εₙ P(Σᵢ εᵢ xᵢ)`. Take the multiset `x₁, …, xₙ` to be `e₁` with multiplicity `k₁`, …, `eₙ` with multiplicity `kₙ`, so `Σ kᵢ = n`. Then `a_k = (n! / ∏ kᵢ!) · L(e₁^{k₁}, …, eₙ^{kₙ})`, and `‖Σᵢ εᵢ xᵢ‖₁ ≤ Σⱼ kⱼ = n`, so by homogeneity `|P(Σᵢ εᵢ xᵢ)| ≤ nⁿ`. Hence `|L(e₁^{k₁}, …, eₙ^{kₙ})| ≤ (1/(2ⁿ n!)) · 2ⁿ · nⁿ = nⁿ / n!`, and `|a_k| ≤ (n! / ∏ kᵢ!) · (nⁿ / n!) = nⁿ / ∏ kᵢ!`. The genuinely open content of Problem 74, the exact best constant `C*(n, k) = sup { |a_k| : ‖P‖ ≤ 1 }`, is NOT formalized in Lean: no closed form for `C*` is known. In particular the bound filed here is not sharp for all `k`: for `k = (n, 0, …, 0)` with `n ≥ 2`, the best constant is `1` (since `|a_k| = |P(e₁)| ≤ 1`) while the bound is `nⁿ / n! > 1`. So no sharpness, attainment, or `IsLeast` clause with the constant `nⁿ / ∏ kᵢ!` may be added (it would be false), and a bare `∃ C, IsLeast …` clause would be resolved-true and formalize nothing open. The monomial gives the lower bound `C*(n, k) ≥ nⁿ / ∏ kᵢ^{kᵢ}` (with `0^0 := 1`).
