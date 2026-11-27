# Formula for the $p$-adic Hilbert symbol

Let $p$ be a prime and let $a, b \in \mathbb{Q}_p^\times$. Write $a = p^\alpha u$ and $b = p^\beta v$
with $\alpha, \beta \in \mathbb{Z}$ and $u, v$ units of $\mathbb{Z}_p$, and let $(a, b)_p$ be the
$p$-adic Hilbert symbol: $1$ if $a x^2 + b y^2 = 1$ has a solution in $\mathbb{Q}_p$, and $-1$
otherwise.

- If $p$ is odd, then

    $$(a, b)_p = (-1)^{\alpha \beta (p-1)/2} \left(\frac{\bar u}{p}\right)^{\beta} \left(\frac{\bar v}{p}\right)^{\alpha},$$

    where $\bar u, \bar v$ are the residues of $u, v$ modulo $p$ and
    $\left(\frac{\cdot}{p}\right)$ is the Legendre symbol.

- If $p = 2$, then

    $$(a, b)_2 = (-1)^{\varepsilon(u)\varepsilon(v) + \alpha\,\omega(v) + \beta\,\omega(u)},$$

    where, for a unit $z$ of $\mathbb{Z}_2$, $\varepsilon(z)$ and $\omega(z)$ are the classes modulo
    $2$ of $(z - 1)/2$ and $(z^2 - 1)/8$; both depend only on $z$ modulo $8$.

For nonzero $a, b$ the symbol defined by $a x^2 + b y^2 = 1$ is $1$ exactly when $z^2 - a x^2 - b y^2$ has a nonzero zero in $\mathbb{Q}_p^3$: a solution $(x, y)$ gives
the zero $(x, y, 1)$, and a nonzero zero with $z = 0$ makes $a x^2 + b y^2$ a hyperbolic plane, which
takes the value $1$.

This is J.-P. Serre's Theorem 1 (*A Course in Arithmetic*, Chapter III, §1.2, p. 20) for
$k = \mathbb{Q}_p$. It is proved by first reducing to $\alpha, \beta \in \{0, 1\}$, since both sides are
unchanged when $a$ or $b$ is multiplied by a square. The proof then uses the description of
$\{a : (a, b)_p = 1\}$ as the group of norms from $\mathbb{Q}_p(\sqrt b)$, and the identities
$(a, b)_p = (b, a)_p$, $(a, b)_p = (a, -ab)_p$ and, when $(a, b)_p = 1$, $(a a', b)_p = (a', b)_p$ that
follow from it. For odd $p$ the remaining values are $(u, v)_p = 1$, the triviality of the symbol on
units, and $(p, v)_p = \left(\frac{\bar v}{p}\right)$, derived below; the case
$\alpha = \beta = 1$ also uses $\left(\frac{-1}{p}\right) = (-1)^{(p-1)/2}$. For $p = 2$ the values
$(u, v)_2$ and $(2, u)_2$ come from the same primitive-solution step and the fact that a unit of
$\mathbb{Z}_2$ is a square exactly when it is $\equiv 1 \pmod 8$.

Derivation of $(p, v)_p = \left(\frac{\bar v}{p}\right)$ for odd $p$ and a unit $v$ of $\mathbb{Z}_p$.
If $\bar v$ is a square modulo $p$, then $v$ is a square in $\mathbb{Z}_p$, by Hensel's lemma applied
to $X^2 - v$, and $(p, v)_p = 1$. Conversely, let $z^2 = p x^2 + v y^2$ have a nonzero solution in
$\mathbb{Q}_p^3$. Multiplying it by a power of $p$ gives a solution in $\mathbb{Z}_p^3$ that is primitive:
not all of $x, y, z$ lie in $p\mathbb{Z}_p$. If $y \in p\mathbb{Z}_p$, then $z \in p\mathbb{Z}_p$, since
$z^2 \equiv v y^2 \pmod p$; then $p^2$ divides $p x^2$, so $x \in p\mathbb{Z}_p$ too, which is
impossible. So $y$ is a unit, hence so is $z$, and reducing modulo $p$ gives
$\bar v = (\bar z / \bar y)^2$, a square. Hence $(p, v)_p = 1$ exactly when $\bar v$ is a square modulo
$p$, that is, when $\left(\frac{\bar v}{p}\right) = 1$.

## Depends on

- [The $p$-adic Hilbert symbol](padic-hilbert-symbol.md), for $(a, b)_p$
- [The ring of p-adic integers](../p-adic-integers.md), for the units $u, v$ of $\mathbb{Z}_p$ and their residues
- [Legendre symbol](../../congruences/power-residues-reciprocity/legendre-symbol-and-euler-s-criterion/legendre-symbol.md), for $\left(\frac{\bar u}{p}\right)$ and $\left(\frac{\bar v}{p}\right)$

## Proof depends on

- [The Hilbert symbol and norms from a quadratic extension](hilbert-symbol-norm-criterion.md), for the description of $\{a : (a, b)_p = 1\}$ as a group of norms
- [First properties of the Hilbert symbol](hilbert-symbol-first-properties.md), for $(a, b)_p = (b, a)_p$, $(a, b)_p = (a, -ab)_p$ and, when $(a, b)_p = 1$, $(a a', b)_p = (a', b)_p$
- [Hensel's lemma with a derivative bound](../../../RingTheory/valuation-rings/henselian-rings-and-hensel-s-lemma/exists-is-root-of-two-mul-add-val-deriva.md), applied to $X^2 - u$ over the complete discrete valuation ring $\mathbb{Z}_p$, for the squares of $\mathbb{Q}_p$ and $\mathbb{Q}_2$
- [The Hilbert symbol of two $p$-adic units is trivial for odd $p$](hilbert-symbol-units-eq-one-of-odd.md), for $(u, v)_p = 1$
- [A p-adic integer is a unit if and only if its p-adic absolute value is 1](../p-adic-integers-units-absolute-value-one.md), for the units $y$ and $z$ of a primitive solution
- [Kernel of reduction modulo p on the p-adic integers](../reduction-modulo-p-kernel.md), for the residues $\bar y \neq 0$ and $\bar z$ and the identity $\bar z^2 = \bar v\,\bar y^2$
- [Euler's criterion](../../congruences/power-residues-reciprocity/legendre-symbol-and-euler-s-criterion/euler-criterion.md), for $\left(\frac{-1}{p}\right) = (-1)^{(p-1)/2}$

## Sources

- J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973: Chapter III,
  §1.1, the definition of the symbol and Propositions 1 and 2, p. 19, and §1.2, Theorem 1, p. 20 (the
  formula, as stated above); Chapter II, §3 (the multiplicative group of $\mathbb{Q}_p$, with
  $\varepsilon$, $\omega$ and the Legendre symbol of a unit in §3.3), pp. 15–19. The proof outline and
  the derivation of $(p, v)_p$ above are written out here; Serre's proof of Theorem 1 begins on p. 20.
