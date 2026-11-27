# Formula for the $2$-adic Hilbert symbol

Let $a, b \in \mathbb{Q}_2^\times$. Write $a = 2^\alpha u$ and $b = 2^\beta v$ with
$\alpha, \beta \in \mathbb{Z}$ and $u, v$ units of $\mathbb{Z}_2$, and let $(a, b)_2$ be the
$2$-adic Hilbert symbol: $1$ if $a x^2 + b y^2 = 1$ has a solution in $\mathbb{Q}_2$, and $-1$
otherwise. Then

$$(a, b)_2 = (-1)^{\varepsilon(u)\varepsilon(v) + \alpha\,\omega(v) + \beta\,\omega(u)},$$

where, for a unit $z$ of $\mathbb{Z}_2$, $\varepsilon(z)$ and $\omega(z)$ are the classes modulo
$2$ of $(z - 1)/2$ and $(z^2 - 1)/8$; both depend only on $z$ modulo $8$.

For nonzero $a, b$ the symbol defined by $a x^2 + b y^2 = 1$ is $1$ exactly when
$z^2 - a x^2 - b y^2$ has a nonzero zero in $\mathbb{Q}_2^3$: a solution $(x, y)$ gives the zero
$(x, y, 1)$, and a nonzero zero with $z = 0$ makes $a x^2 + b y^2$ a hyperbolic plane, which takes
the value $1$.

This is J.-P. Serre's Theorem 1 (*A Course in Arithmetic*, Chapter III, §1.2, p. 20) for
$k = \mathbb{Q}_2$. It is proved by first reducing to $\alpha, \beta \in \{0, 1\}$, since both sides
are unchanged when $a$ or $b$ is multiplied by a square. The proof then uses the description of
$\{a : (a, b)_2 = 1\}$ as the group of norms from $\mathbb{Q}_2(\sqrt b)$, and the identities
$(a, b)_2 = (b, a)_2$, $(a, b)_2 = (a, -ab)_2$ and, when $(a, b)_2 = 1$, $(a a', b)_2 = (a', b)_2$
that follow from it. The remaining values $(u, v)_2$ and $(2, u)_2$ come from a primitive-solution
step: a nonzero solution of $z^2 = a x^2 + b y^2$ in $\mathbb{Q}_2^3$ is multiplied by a power of $2$
to a solution in $\mathbb{Z}_2^3$ not all of whose coordinates lie in $2\mathbb{Z}_2$, which is then
reduced modulo $8$, together with the fact that a unit of $\mathbb{Z}_2$ is a square exactly when it
is $\equiv 1 \pmod 8$.

## Depends on

- [The $p$-adic Hilbert symbol](padic-hilbert-symbol.md), for $(a, b)_2$
- [The ring of p-adic integers](../p-adic-integers.md), for the units $u, v$ of $\mathbb{Z}_2$ and their classes modulo $8$

## Proof depends on

- [The Hilbert symbol and norms from a quadratic extension](hilbert-symbol-norm-criterion.md), for the description of $\{a : (a, b)_2 = 1\}$ as a group of norms
- [First properties of the Hilbert symbol](hilbert-symbol-first-properties.md), for $(a, b)_2 = (b, a)_2$, $(a, b)_2 = (a, -ab)_2$ and, when $(a, b)_2 = 1$, $(a a', b)_2 = (a', b)_2$
- [Hensel's lemma with a derivative bound](../../../RingTheory/valuation-rings/henselian-rings-and-hensel-s-lemma/exists-is-root-of-two-mul-add-val-deriva.md), applied to $X^2 - u$ over the complete discrete valuation ring $\mathbb{Z}_2$, for the squares of $\mathbb{Q}_2$
- [A p-adic integer is a unit if and only if its p-adic absolute value is 1](../p-adic-integers-units-absolute-value-one.md), for the units among the coordinates of a primitive solution
- [Kernel of reduction modulo p on the p-adic integers](../reduction-modulo-p-kernel.md), for the coordinates of a primitive solution that lie in $2\mathbb{Z}_2$

## Sources

- J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973: Chapter III,
  §1.1, the definition of the symbol and Propositions 1 and 2, p. 19, and §1.2, Theorem 1, p. 20 (the
  formula, the case $p = 2$, with $\varepsilon$ and $\omega$ as recalled after the theorem);
  Chapter II, §3 (the multiplicative group of $\mathbb{Q}_p$, with $\varepsilon$ and $\omega$ in
  §3.3), pp. 15–19. The proof outline above is written out here; Serre's proof of Theorem 1 begins
  on p. 20.
