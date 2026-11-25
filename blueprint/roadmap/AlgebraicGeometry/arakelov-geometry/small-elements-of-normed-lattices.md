# Small elements of normed lattices

This node is still to be broken down: the statements below are precise, but their proofs rest on
estimates from the geometry of numbers that are not yet broken down.

A normed finitely generated $\mathbb{Z}$-module $(M, \lVert \cdot \rVert)$ is a finitely generated
$\mathbb{Z}$-module $M$ with a norm on $M_\mathbb{R} = M \otimes_\mathbb{Z} \mathbb{R}$. Put $B(M,
\lVert \cdot \rVert) = \{ x \in M_\mathbb{R} : \lVert x \rVert \le 1 \}$,

$$\hat h^0(M, \lVert \cdot \rVert) = \log \#\{ x \in M : \lVert x \rVert \le 1 \}, \qquad
\hat\chi(M, \lVert \cdot \rVert) = \log \frac{\operatorname{vol}(B(M, \lVert \cdot \rVert))}
{\operatorname{vol}(M_\mathbb{R} / (M / M_{\mathrm{tor}}))} + \log \# M_{\mathrm{tor}},$$

where $\lVert x \rVert$ means the norm of the image of $x$ in $M_\mathbb{R}$, and $\hat h^1(M,
\lVert \cdot \rVert) = \hat h^0(M^\vee, \lVert \cdot \rVert^\vee)$ for the dual module $M^\vee =
\operatorname{Hom}_\mathbb{Z}(M, \mathbb{Z})$ with the dual norm $\lVert \varphi \rVert^\vee = \sup
\{ |\varphi(x)| : x \in B(M, \lVert \cdot \rVert) \}$. Then (Moriwaki, Proposition 2.1):

1. $-\log(6) \operatorname{rk} M \le \hat h^0(M) - \hat h^1(M) - \hat\chi(M) \le \log(3/2)
   \operatorname{rk} M + 2 \log((\operatorname{rk} M)!)$;
2. if $\lVert \cdot \rVert_1 \le \lVert \cdot \rVert_2$, then $\hat h^0(M, \lVert \cdot \rVert_1)
   \ge \hat h^0(M, \lVert \cdot \rVert_2)$, $\hat h^1(M, \lVert \cdot \rVert_1) \le \hat h^1(M,
   \lVert \cdot \rVert_2)$ and $\hat\chi(M, \lVert \cdot \rVert_2) - \hat\chi(M, \lVert \cdot
   \rVert_1) \le \hat h^0(M, \lVert \cdot \rVert_2) - \hat h^0(M, \lVert \cdot \rVert_1) + \log(9)
   \operatorname{rk} M + 2 \log((\operatorname{rk} M)!)$;
3. for a real number $\lambda \ge 0$, $0 \le \hat h^0(M, e^{-\lambda} \lVert \cdot \rVert) - \hat
   h^0(M, \lVert \cdot \rVert) \le \lambda \operatorname{rk} M + \log(9) \operatorname{rk} M + 2
   \log((\operatorname{rk} M)!)$;
4. for an exact sequence $0 \to (M', \lVert \cdot \rVert') \to (M, \lVert \cdot \rVert) \to (M'',
   \lVert \cdot \rVert'') \to 0$ of finitely generated $\mathbb{Z}$-modules that is an exact
   sequence of normed real vector spaces after $\otimes \mathbb{R}$, that is, $M'_\mathbb{R}$
   carries the subnorm and $M''_\mathbb{R}$ the quotient norm of $\lVert \cdot \rVert$ (Moriwaki,
   Conventions and terminology 3, p. 4); linear exactness with arbitrary norms is not enough, $\hat
   h^0(M) \le \hat h^0(M') + \hat h^0(M'') + \log(18) \operatorname{rk} M' + 2
   \log((\operatorname{rk} M')!)$;
5. if $M / M_{\mathrm{tor}}$ has a basis of elements of norm at most $1$, then $\hat h^1(M) \le
   \log(3) \operatorname{rk} M$.

Moreover, for a free $\mathbb{Z}$-module $M$ of rank $m$ and the open unit ball, Minkowski's theorem
gives $\log \#\{ x \in M : \lVert x \rVert < 1 \} \ge \log (\operatorname{vol}\{ \lVert x \rVert < 1
\} / \operatorname{covol}(M)) - m \log 2$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Minkowski's convex body theorem](../../NumberTheory/diophantine-approximation/uniform-distribution-metric/minkowski-convex-body-theorem.md),
  for Minkowski's first theorem, a nonzero element of $M$ in a symmetric convex body of volume more
  than $2^m \operatorname{covol}(M)$; the lower bound for the number of points of $M$ in the open
  unit ball is a further step

## Expansion

A good expansion has pages for:

- the counting form of Minkowski's first theorem behind the last inequality, a lower bound for the
  number of lattice points in the open unit ball (Yuan, Remark 2 after Definition 2.1 and
  Proposition 2.6 (1));
- Minkowski's second theorem on successive minima, which Zhang uses to compare the covolumes of
  lattices of different ranks (Zhang, (1.7));
- Mahler's inequality $V(K) V(K^*) \ge 4^n / (n!)^2$ for a convex symmetric body $K \subset
  \mathbb{R}^n$ and its polar body $K^*$, and Gillet and Soulé's estimates for the numbers of
  lattice points in $K$ and $K^*$, from which Moriwaki deduces items 1–5 (Moriwaki, proof of
  Proposition 2.1, pp. 13–14).

## Sources

- A. Moriwaki, "Continuity of volumes on arithmetic varieties", J. Algebraic Geom. 18 (2009),
  407–457, arXiv:math/0612269 (version 2), <https://arxiv.org/abs/math/0612269v2>: §2 (normed
  finitely generated $\mathbb{Z}$-modules, $\hat h^0$, $\hat h^1$, $\hat\chi$), pp. 12–13;
  Proposition 2.1 with its proof (via Gillet–Soulé's Theorem 1 and Proposition 4 and Mahler's
  inequality), pp. 13–14; Remark 2.2, p. 15.
- X. Yuan, "Big line bundles over arithmetic varieties", Invent. Math. 173 (2008), 603–649,
  arXiv:math/0612424 (version 2), <https://arxiv.org/abs/math/0612424v2>: Remark 2 after Definition
  2.1, p. 10, and Proposition 2.6 (1) with its proof ("It is just Minkowski's theorem"), p. 13.
- H. Gillet and C. Soulé, "On the number of lattice points in convex symmetric bodies and their
  duals", Israel J. Math. 74 (1991), 347–357, as cited by Moriwaki; and the later erratum, Israel J.
  Math. 171 (2009), 443–444, which rejects an error-free subadditivity derived from another
  proposition, not the estimates above.
- S.-W. Zhang, "Positive line bundles on arithmetic varieties", J. Amer. Math. Soc. 8 (1995),
  187–221, author's scan of the printed edition
  <https://web.math.princeton.edu/~shouwu/publications/plav.pdf>: (1.7), p. 191 (successive minima).
