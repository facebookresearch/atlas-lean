# Order of the unitary group over a finite field

Let $q$ be a prime power, let $x \mapsto \bar{x} = x^q$ be the nontrivial automorphism of $\mathbb{F}_{q^2}$ over $\mathbb{F}_q$,
and let $h$ be a nondegenerate Hermitian form on an $\mathbb{F}_{q^2}$-vector space $W$ of dimension $m \ge 1$: $h$ is
$\mathbb{F}_{q^2}$-linear in its first variable, $h(y, x) = \overline{h(x, y)}$, and $h(x, W) = 0$ only for $x = 0$. Then the
unitary group of $(W, h)$, the group of $\mathbb{F}_{q^2}$-linear automorphisms $g$ of $W$ with $h(gx, gy) = h(x, y)$, has order

$$\# \mathrm{U}(W, h) = q^{m(m-1)/2} \prod_{j=1}^{m} \bigl(q^j - (-1)^j\bigr), \qquad \text{so} \qquad q^{-m^2} \, \# \mathrm{U}(W, h) = \prod_{j=1}^{m} \bigl(1 - (-q)^{-j}\bigr).$$

The norm $N(x) = x \bar{x} = x^{q+1}$ maps $\mathbb{F}_{q^2}^\times$ to $\mathbb{F}_q^\times$, as $N(x)^q = x^{q^2 + q} = x \cdot x^q = N(x)$;
its kernel, the set of roots of $X^{q+1} - 1$, has at most $q + 1$ elements by the
[bound on the number of roots](../../Algebra/zeros-of-polynomials/card-roots-le-degree.md), so its image has at least
$(q^2 - 1)/(q + 1) = q - 1$ elements: the norm maps $\mathbb{F}_{q^2}^\times$ onto $\mathbb{F}_q^\times$, each value being taken
exactly $q + 1$ times.
Some $x \in W$ has $h(x, x) \neq 0$: otherwise $h(x + y, x + y) = 0$ gives $h(x, y) + \overline{h(x, y)} = 0$ for all
$x, y$, and replacing $x$ by $\alpha x$ shows that the trace of $\alpha h(x, y)$ to $\mathbb{F}_q$ vanishes for every
$\alpha \in \mathbb{F}_{q^2}$, so $h = 0$, as the trace form of $\mathbb{F}_{q^2}/\mathbb{F}_q$ is nondegenerate. Rescaling such an $x$
by the surjectivity of the norm gives a vector with $h(x, x) = 1$, whose orthogonal complement is again nondegenerate,
of dimension $m - 1$. So $W$ has an orthonormal basis, the unitary group acts simply transitively on the ordered
orthonormal bases, and choosing their vectors one at a time gives $\# \mathrm{U}(W, h) = \prod_{k=1}^{m} u_k$, where $u_k$ is
the number of $x \in \mathbb{F}_{q^2}^k$ with $\sum_i x_i \bar{x}_i = 1$. Let $a_k(c)$ be the number of $x \in \mathbb{F}_{q^2}^k$ with
$\sum_i x_i \bar{x}_i = c$. Then $a_k(c) = a_k(1) = u_k$ for every $c \neq 0$, by rescaling, $a_1(0) = 1$,
$a_k(0) + (q - 1) a_k(1) = q^{2k}$, and splitting off the last coordinate gives
$a_k(0) = a_{k-1}(0) + (q - 1)(q + 1) a_{k-1}(1) = (q + 1) q^{2k-2} - q \, a_{k-1}(0)$. By induction
$a_k(0) = q^{2k-1} + (-1)^k (q^k - q^{k-1})$, hence $u_k = q^{k-1} (q^k - (-1)^k)$, and the product of the $u_k$ is the
stated order. (The count is carried out here; Kirschmer's table gives the order.)

## Depends on

This node has no prerequisites.

## Proof depends on

- [Trace form criterion for étale algebras](../../RingTheory/algebras-and-differentials/tale-algebras-and-the-trace-form/trace-form-nondegenerate-iff-etale.md), for the nondegeneracy of the trace form of the finite separable, hence étale, extension $\mathbb{F}_{q^2}/\mathbb{F}_q$
- [A polynomial over an integral domain has at most as many roots as its degree](../../Algebra/zeros-of-polynomials/card-roots-le-degree.md), for the kernel of the norm

## Sources

- M. Kirschmer, *Definite quadratic and hermitian forms with small class number*, Habilitationsschrift,
  RWTH Aachen University (2016), <http://www.math.rwth-aachen.de/~Markus.Kirschmer/papers/herm.pdf>, Section 4.2,
  the table of dimensions and numbers of points after Lemma 4.2.5 (p. 53): $\dim \mathrm{U}_m = m^2$ and
  $\# \mathrm{U}_m(\mathbb{F}_q) = q^{m(m-1)/2} \prod_{j=1}^m (q^j - (-1)^j)$, for the unitary group in $m$ variables over
  $\mathbb{F}_q$.
