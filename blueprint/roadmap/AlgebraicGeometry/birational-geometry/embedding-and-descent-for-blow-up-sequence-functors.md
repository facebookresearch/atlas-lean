# Embeddings and descent for blow-up sequence functors

The following three statements, all over a field $k$, are the auxiliary results by which Kollár
constructs a functorial resolution from principalization.

1. (Descent, Kollár's Proposition 37.) Let $B$ be a
   [blow-up sequence functor](simple-normal-crossing-divisor.md) defined on affine schemes over $k$ that
   commutes with smooth surjections. Then $B$ has a unique extension to a blow-up sequence functor
   defined on all schemes of finite type over $k$ and commuting with smooth surjections.
2. (Kollár's Lemma 39.) Let $X$ be an affine scheme and $i_1 \colon X \hookrightarrow \mathbb{A}^n$,
   $i_2 \colon X \hookrightarrow \mathbb{A}^m$ two closed embeddings. Then the two embeddings
   $X \hookrightarrow \mathbb{A}^n \hookrightarrow \mathbb{A}^{n+m}$ and
   $X \hookrightarrow \mathbb{A}^m \hookrightarrow \mathbb{A}^{n+m}$ into coordinate subspaces are
   equivalent under a (nonlinear) automorphism of $\mathbb{A}^{n+m}$.
3. (Kollár's Lemma 41.) Let $h \colon Y \to X$ be a smooth morphism, $y \in Y$ a point and
   $i \colon X \hookrightarrow A_X$ a closed embedding into a smooth scheme. Then there are open
   neighbourhoods $y \in Y^0 \subset Y$ and $h(y) \in A_X^0 \subset A_X$, with $X^0 = X \cap A_X^0$, a
   smooth morphism $h_A \colon A_Y^0 \to A_X^0$ and a closed embedding $j \colon Y^0 \hookrightarrow
   A_Y^0$ such that $Y^0 = X^0 \times_{A_X^0} A_Y^0$, compatibly with $h$, $i$, $j$ and $h_A$.

For 1, Kollár covers $X$ by affine opens $U_i$, applies $B$ to the affine scheme
$X' = \coprod_i U_i$, which maps to $X$ by a smooth surjection, and shows that $B(X')$ descends to $X$
because its two pull-backs to $X' \times_X X' = \coprod_{i, j} U_i \cap U_j$ agree; this is why the
functor must be defined on disconnected affine schemes (Warning 38). For 2, extend $i_1$ to a morphism
$j_1 \colon \mathbb{A}^m \to \mathbb{A}^n$ and $i_2$ to $j_2 \colon \mathbb{A}^n \to \mathbb{A}^m$, and
compose the automorphisms $(x, y) \mapsto (x, y + j_2(x))$ and $(x, y) \mapsto (x - j_1(y), y)$. For 3,
Kollár works locally with a general linear projection, over infinite fields, the only case he uses.

## Depends on

- [Simple normal crossing divisor](simple-normal-crossing-divisor.md), for blow-up sequences and blow-up
  sequence functors

## Sources

- J. Kollár, "Resolution of singularities – Seattle lecture", arXiv:math/0508332 (version 3),
  <https://arxiv.org/abs/math/0508332v3>: Proposition 37 with its proof and Warning 38, p. 26;
  Lemma 39 with its proof and Lemma 41 with its proof (over infinite fields), p. 27.
