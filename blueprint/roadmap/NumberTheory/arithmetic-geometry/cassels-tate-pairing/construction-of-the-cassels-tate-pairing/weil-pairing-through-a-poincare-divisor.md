# The Weil pairing through a Poincaré divisor

Let $k$ be a field with algebraic closure $\bar k$, $m \ge 1$ an integer not divisible by the characteristic of $k$,
$A$ an [abelian variety](../../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md) over $k$ and $A^\vee$ its
[dual abelian variety](../../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md). A **Poincaré divisor** is
a $k$-rational divisor $\mathcal{P}$ on $A \times A^\vee$ whose line bundle is the Poincaré bundle; one exists, as the
Poincaré bundle is defined over $k$ and $A \times A^\vee$ is integral, and two of them differ by the divisor of a function.

For $0$-cycles $\mathfrak{b} = \sum_i n_i x_i$ on $A_{\bar k}$ and $\mathfrak{b}' = \sum_j n'_j y_j$ on $A^\vee_{\bar k}$ of degree $0$,
with $\mathfrak{b}$ summing to $0$ in $A(\bar k)$, the divisor $\mathcal{P}(\mathfrak{b}) = \sum_i n_i \mathcal{P}(x_i)$ on
$A^\vee_{\bar k}$, where $\mathcal{P}(x)$ is the pull-back of $\mathcal{P}$ along $y \mapsto (x, y)$, is the divisor of a
function $f$, and $\mathcal{P}(\mathfrak{b}, \mathfrak{b}') = \prod_j f(y_j)^{n'_j}$ when this is defined; it does not depend on
the constant in $f$. Define ${}^t\mathcal{P}(\mathfrak{b}', \mathfrak{b})$ in the same way with the transpose ${}^t\mathcal{P}$ on
$A^\vee \times A$, for $\mathfrak{b}'$ summing to $0$ in $A^\vee(\bar k)$.

The **Weil pairing** is the map

$$e_m \colon A[m](\bar k) \times A^\vee[m](\bar k) \to \mu_m(\bar k), \qquad e_m(x, x') = \frac{\mathcal{P}(m\mathfrak{a}, \mathfrak{a}')}{{}^t\mathcal{P}(m\mathfrak{a}', \mathfrak{a})},$$

where $\mathfrak{a}$ and $\mathfrak{a}'$ are $0$-cycles of degree $0$ on $A_{\bar k}$ and $A^\vee_{\bar k}$ summing to $x$ and $x'$,
chosen so that both values are defined; $m\mathfrak{a}$ and $m\mathfrak{a}'$ sum to $mx = 0$ and $mx' = 0$. Poonen and Stoll
write it additively, $e_m(x, x') = (m\mathfrak{a}) \cup \mathfrak{a}' - \mathfrak{a} \cup (m\mathfrak{a}')$, and note that it is the
inverse of Lang's.

The value does not depend on $\mathfrak{a}$, $\mathfrak{a}'$ or $\mathcal{P}$, and lies in $\mu_m$:

- Replacing $\mathfrak{a}$ by $\mathfrak{a} + \mathfrak{y}$ with $\mathfrak{y}$ of degree $0$ summing to $0$ multiplies the value by
  $\mathcal{P}(m\mathfrak{y}, \mathfrak{a}') / {}^t\mathcal{P}(m\mathfrak{a}', \mathfrak{y})$. As $\mathcal{P}(m\mathfrak{y})$ is the divisor of
  $f^m$, $\mathcal{P}(m\mathfrak{y}, \mathfrak{a}') = \mathcal{P}(\mathfrak{y}, m\mathfrak{a}')$, which equals
  ${}^t\mathcal{P}(m\mathfrak{a}', \mathfrak{y})$ by Lang's reciprocity law, $m\mathfrak{a}'$ summing to $0$. The same argument
  applies to $\mathfrak{a}'$.
- Replacing $\mathcal{P}$ by $\mathcal{P} + (F)$ multiplies $\mathcal{P}(\mathfrak{b}, \mathfrak{b}')$ and
  ${}^t\mathcal{P}(\mathfrak{b}', \mathfrak{b})$ by the same value $F(\mathfrak{b} \times \mathfrak{b}') = \prod_{i,j} F(x_i, y_j)^{n_i n'_j}$,
  and $F(m\mathfrak{a} \times \mathfrak{a}') = F(\mathfrak{a} \times m\mathfrak{a}')$.
- $e_m(x, x')^m = \mathcal{P}(m\mathfrak{a}, m\mathfrak{a}') / {}^t\mathcal{P}(m\mathfrak{a}', m\mathfrak{a}) = 1$ by Lang's reciprocity law.

Poonen and Stoll normalize $e_m$ by an example (their footnote 21): if $E$ is the elliptic curve $\mathbb{C}/(\mathbb{Z} + \mathbb{Z}\tau)$,
identified with its dual, and $P$, $Q$ correspond to $1/m$ and $\tau/m$, then $e_m(P, Q) = e^{-2\pi i/m}$.

## Depends on

- [Abelian scheme](../../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md), for abelian varieties over a field
- [Dual abelian variety](../../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md), for $A^\vee$ and the Poincaré bundle (its item 1)
- [Isogenies of abelian schemes](../../../../AlgebraicGeometry/abelian-varieties/isogenies-of-abelian-schemes.md), for the kernels $A[m]$ and $A^\vee[m]$ of multiplication by $m$

## Proof depends on

- [Lang's reciprocity law for divisors on a product](lang-reciprocity-law.md), for the independence of $\mathfrak{a}$ and $\mathfrak{a}'$ and for $e_m^m = 1$

## Sources

- B. Poonen and M. Stoll, *The Cassels-Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999),
  1109–1149, doi:10.2307/121064: §12.2, "The Weil pairing definition", p. 1143 (the definition of $e_m$, citing Lang,
  with footnote 21 on its normalization and footnote 22 on the additive notation); §12.1, p. 1143 (the two pairings
  $\cup$, which agree where both are defined by Lang reciprocity); §2, p. 1114 (the values $D(\mathfrak{a}, \mathfrak{a}')$);
  §12, p. 1142 (choices are made so that the pairings are defined, "It is not difficult to see that this is always possible").
- S. Lang, *Abelian Varieties*, Springer-Verlag, 1983, p. 173, as cited by Poonen and Stoll, §12.2, p. 1143; not read.
