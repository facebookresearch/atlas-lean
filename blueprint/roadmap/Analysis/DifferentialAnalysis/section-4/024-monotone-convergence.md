---
article_id: af_edf2e648d7c364db7be43eed
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MonotoneConvergence.monotone_convergence_theorem'
---

# Theorem 4.3 (Monotone Convergence)

Let $f_n$ be an increasing sequence of non-negative measurable (extended) functions, then $f(x) = \lim_{n \to \infty} f_n(x)$ is measurable and $$\int_{E} f\, d\mu = \lim_{n \to \infty} \int_{E} f_n\, d\mu$$ for any measurable set $E \subset X$.

## Depends on

- [Definition 4.1](022-definition-4-1.md)

## Proof depends on

- [Lemma 3.1](../section-3/019-lemma-3-1.md)

## Sources

- [MIT 18.155 Differential Analysis (Fall 2004), Section 4](../../../../sources/v1/DifferentialAnalysis.md)
