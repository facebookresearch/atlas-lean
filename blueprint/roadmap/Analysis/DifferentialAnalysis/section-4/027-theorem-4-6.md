---
article_id: af_ed5a9a414830aa3a7545b93f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: DominatedConvergence.dominated_convergence_integrable_and_tendsto
---

# Theorem 4.6

If $f_n$ is a sequence of integrable functions, $f_k \to f$ a.e. and $|f_n| \leq g$ for some integrable $g$ then $f$ is integrable and $$\int f\, d\mu = \lim_{n \to \infty} \int f_n\, d\mu.$$

## Depends on

- [Definition 4.4](025-definition-4-4.md)

## Proof depends on

- [Theorem 4.3 (Monotone Convergence)](024-monotone-convergence.md)
- [Lemma 4.5 (Fatou)](026-fatou.md)

## Sources

- [MIT 18.155 Differential Analysis (Fall 2004), Section 4](../../../../sources/v1/DifferentialAnalysis.md)
