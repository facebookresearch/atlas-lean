# Height bound for points of a Belyi curve above small rational numbers

This node is still to be broken down. For a nonzero rational number $a = p/q$ with $p, q$ coprime
integers and $q > 0$, let $h_{\mathrm{naive}}(a) = \log \max(\lvert p \rvert, \lvert q \rvert)$.
Let $Y$ be a smooth projective connected curve over $\overline{\mathbb{Q}}$ of genus $g \ge 1$ and
$\pi \colon Y \to \mathbb{P}^1_{\overline{\mathbb{Q}}}$ a finite morphism of degree $d$ that is
unramified over $\mathbb{P}^1_{\overline{\mathbb{Q}}} \setminus \{0, 1, \infty\}$ (a
[Belyi map](is-belyi-map.md)). Then for every rational number $0 < a \le \frac23$ and every $b
\in Y(\overline{\mathbb{Q}})$ lying over $a$, the
[height](../arakelov-invariants-of-curves/arakelov-invariants-of-a-curve.md) of $b$ satisfies

$$h(b) \le 3 \, h_{\mathrm{naive}}(a) \, d^2 + 6378031 \, \frac{d^5}{g}.$$

## Depends on

- [Belyi map](is-belyi-map.md)
- [Arakelov invariants of a curve over $\overline{\mathbb{Q}}$](../arakelov-invariants-of-curves/arakelov-invariants-of-a-curve.md), for the
  height of a point

## Proof depends on

- [Models of covers of the projective line with small vertical branch locus](wild-models-of-covers.md)
- [Lenstra's bound for the different](../../../NumberTheory/algebraic-number-theory/discriminants-ramification/lenstra-s-bound-for-the-different.md)
- [Bound for the Arakelov–Green function of a Belyi cover](green-function-bound-for-belyi-covers.md)
- [Belyi covers of the modular curve $X(2)$](belyi-cover-of-x2.md), to view $\lambda^{-1} \circ
  \pi_\sigma$ as a Belyi cover

The other inputs are listed under Expansion.

## Expansion

The proof bounds $h(b) [K : \mathbb{Q}] \le (P', K_{\mathcal{Y}'})_{\mathrm{fin}} + \sum_\sigma
(-\log \lVert d\pi_K \rVert_\sigma)(\sigma(b))$ on the model of the first prerequisite; the finite
part is at most $3 h_{\mathrm{naive}}(a) d^2 + 2 d^3$ per degree and the archimedean part at most
$6378027 \, d^5 / g + 2$. A good expansion has pages for: Lemma 2.3.1, that the height of a point
does not decrease on another regular model (p. 99); Propositions 4.2.2 and 4.2.4 and Lemmas 4.2.1
and 4.2.3, bounding the finite part through the different (pp. 113–118), with Proposition 4.1.3
(p. 113); and Lemma 4.4.1 on the $q$-expansion of the modular lambda function, giving $-\log \lVert
d(\lambda \circ \pi) \rVert_{\mathrm{Ar}} \le -\log \lVert dw_y \rVert_{\mathrm{Ar}} + 2$ at points
over $a$, where $\Im(\lambda^{-1}(a)) \ge \Im(\lambda^{-1}(2/3)) > s_1$ (pp. 119–122).

## Sources

- A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8 (2014), 89–140, <https://doi.org/10.2140/ant.2014.8.89>, Theorem 4.5.1 and its proof, pp. 120–122.
