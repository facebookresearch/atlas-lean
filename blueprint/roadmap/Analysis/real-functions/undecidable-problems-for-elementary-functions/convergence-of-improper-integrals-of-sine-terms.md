# Convergence of improper integrals of sine expressions is undecidable

No algorithm decides, for the integer parameter a, whether the improper integral over ℝ of 1/((x² + 1) F_a(x)²) converges, where F_a is the computable family of one-variable sine expressions with undecidable sign behavior.

**Theorem (Wang; π-free form by Laczkovich).** Let $F_a$ ($a \in \mathbb Z$) be the computable family of functions built from the integers and $x$ by addition, multiplication and composition with $\sin$, such that either $F_a > 1$ on $\mathbb R$ or $F_a$ takes values below $-1$ and above $1$, and it is undecidable which. Then it is impossible to decide, given $a$, whether

$$
\int_{-\infty}^{\infty} \frac{dx}{(x^2 + 1)\, F_a(x)^2}
$$

converges.

## Depends on

- [Nonnegativity, positivity and zeros of one-variable sine expressions are undecidable](sign-and-zeros-of-one-variable-sine-terms.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Nonnegativity, positivity and zeros of one-variable sine expressions are undecidable](sign-and-zeros-of-one-variable-sine-terms.md)

## Expansion

If $F_a > 1$ everywhere, the integrand is bounded by $1/(x^2 + 1)$ and the integral converges. Otherwise $F_a$ changes sign, so it has a real zero; since $F_a$ is real analytic, $1/F_a^2$ is not integrable near that zero and the integral diverges. A good expansion links a page for this fact: near a zero of order $m \ge 1$ of a real analytic function, $1/F_a^2$ behaves like $|x - x_0|^{-2m}$.

## Sources

- Paul S. Wang, "The undecidability of the existence of zeros of real elementary functions", *Journal of the ACM* 21(4), 1974, pp. 586–589, <https://doi.org/10.1145/321850.321856> (cited after the survey below).
- B. Poonen, "Undecidable problems: a sampler", in *Interpreting Gödel: Critical Essays* (J. Kennedy, ed.), Cambridge University Press, 2014, pp. 211–241, <https://doi.org/10.1017/CBO9780511756306.015>; read as arXiv:1204.0299v2, <https://arxiv.org/abs/1204.0299v2>: Remark 9.6 in Section 9.3 of that version, with the functions $F_a$ recorded at the end of Section 9.1.3.
