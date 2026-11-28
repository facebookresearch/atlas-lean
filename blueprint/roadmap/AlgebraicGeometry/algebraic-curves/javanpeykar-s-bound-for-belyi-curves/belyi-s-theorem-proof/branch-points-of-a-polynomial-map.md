# Branch points of a polynomial map of the projective line

Let $k$ be an algebraically closed field of characteristic $0$ and $p \in k[z]$ a nonconstant
polynomial, and let $p \colon \mathbb{P}^1_k \to \mathbb{P}^1_k$ also denote the finite morphism
that is $z \mapsto p(z)$ on $\mathbb{A}^1_k = \mathbb{P}^1_k \setminus \{\infty\}$ and maps
$\infty$ to $\infty$. Then $p^{-1}(\infty) = \{\infty\}$, the restriction of $p$ to the open
subscheme $D(p') \subset \mathbb{A}^1_k$ where $p'$ does not vanish is étale, and so $p$ is
unramified over

$$\mathbb{P}^1_k \setminus \bigl( \{\infty\} \cup \{p(r) : r \in k, \ p'(r) = 0\} \bigr).$$

## Depends on

- [Étale morphisms of schemes](../../../schemes-and-morphisms/etale-morphism-of-schemes.md), for the étale
  restriction

## Proof depends on

None among the pages.

## Proof sketch

On $\mathbb{A}^1_k$ the morphism is $\operatorname{Spec} k[z] \to \operatorname{Spec} k[w]$, $w
\mapsto p(z)$, and $k[z] = k[w][z]/(p(z) - w)$. If $a \in k^\times$ is the leading coefficient of
$p$, then $f = a^{-1}(p(z) - w)$ is monic in $z$, and its derivative $a^{-1} p'(z)$ is invertible
in $k[w][z]_{p'}/(f) = k[z]_{p'}$; here $p' \ne 0$, as $p$ is nonconstant and $k$ has
characteristic $0$. So $k[w] \to k[z]_{p'}$ is standard étale, hence étale, and an étale morphism
is unramified. In homogeneous coordinates $p$ is $[x : y] \mapsto [y^d p(x/y) : y^d]$ with $d =
\deg p$, so the fibre over $\infty = [1 : 0]$ is the point $y = 0$. A point of the open set in the
statement has no preimage at $\infty$ or at a zero of $p'$, so its preimages lie in $D(p')$.

## Sources

- The Stacks project, Definition 10.144.1 (Tag 00UB), <https://stacks.math.columbia.edu/tag/00UB>:
  for a ring $R$ and $f, g \in R[x]$ with $f$ monic and $f'$ invertible in $R[x]_g/(f)$, the ring
  map $R \to R[x]_g/(f)$ is standard étale; Lemma 10.144.2 (Tag 00UC),
  <https://stacks.math.columbia.edu/tag/00UC>: a standard étale ring map is étale; Lemma 29.37.5
  (Tag 02GK), <https://stacks.math.columbia.edu/tag/02GK>: a morphism is étale at a point if and
  only if it is smooth and unramified there. With $R = k[w]$, $f = a^{-1}(p(z) - w)$ and $g = p'$
  they give the étale clause for every field $k$.
- B. Köck, *Belyi's theorem revisited*, Beitr. Algebra Geom. 45 (2004), no. 1, 253–265, <https://www.emis.de/ft/11086>, proof of Lemma 3.5, p. 263 ("$S_1 \cup \{\infty\}$ is the set of critical values
  of $p_1$", with $S_1$ the set of values of $p_1$ at the zeros of $p_1'$), and proof of Lemma 3.6,
  p. 263 (the critical values of $q_1$ from the zeros of $q_1'$), for his polynomials over
  $\mathbb{C}$.
