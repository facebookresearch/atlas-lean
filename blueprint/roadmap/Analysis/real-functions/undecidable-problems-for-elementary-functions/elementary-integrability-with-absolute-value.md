# Elementary integrability with absolute value is undecidable

Once the absolute value may be used, no algorithm decides whether an explicit function of one real variable built from sine expressions and the Gaussian has an elementary antiderivative on the whole real line, in contrast with Risch's algorithm for elementary towers.

**Theorem (Richardson; π-free form by Laczkovich).** Let $\sigma(x) = \tfrac12 (|x| - |x - 1| + 1)$, which is $0$ for $x \le 0$, $x$ for $0 < x < 1$ and $1$ for $x \ge 1$, and let $F_a$ be the computable family of one-variable sine expressions, in the class $\mathscr S$ built from the integers and $x$ by addition, multiplication and composition with $\sin$, for which it is undecidable whether $F_a > 1$ everywhere or $F_a$ takes values below $-1$ and above $1$. Then it is impossible to decide, given $a \in \mathbb Z$, whether

$$
\int \sigma(-F_a(x))\, e^{x^2} \, dx
$$

is an elementary function on all of $\mathbb R$.

## Depends on

- [Nonnegativity, positivity and zeros of one-variable sine expressions are undecidable](sign-and-zeros-of-one-variable-sine-terms.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Nonnegativity, positivity and zeros of one-variable sine expressions are undecidable](sign-and-zeros-of-one-variable-sine-terms.md)

## Expansion

If $F_a > 1$ on $\mathbb R$, then $\sigma(-F_a)$ is identically $0$ and the integral is $0$. Otherwise $F_a < -1$ on some open interval, where $\sigma(-F_a) = 1$, and there an antiderivative of $e^{x^2}$ would have to be elementary, which Liouville's theorem forbids (there is no elementary antiderivative of $e^{x^2}$ on any interval). A good expansion links a page for this theorem of Liouville. Deciding which case holds would decide the sign behavior of $F_a$.

## Sources

- Daniel Richardson, "Some undecidable problems involving elementary functions of a real variable", *Journal of Symbolic Logic* 33(4), 1968, pp. 514–520, <https://doi.org/10.2307/2271358>: Section 2, Theorem Three (cited after the survey below).
- B. Poonen, "Undecidable problems: a sampler", in *Interpreting Gödel: Critical Essays* (J. Kennedy, ed.), Cambridge University Press, 2014, pp. 211–241, <https://doi.org/10.1017/CBO9780511756306.015>; read as arXiv:1204.0299v2, <https://arxiv.org/abs/1204.0299v2>: Remark 9.5 in Section 9.3 ("Integration") of that version, with the functions $F_a$ recorded at the end of Section 9.1.3.
