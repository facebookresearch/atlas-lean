# The function i_G of a quotient

Let $L/K$ be a finite Galois extension of complete discretely valued fields whose residue fields are perfect
of characteristic $p > 0$, with group $G$, and let $i_G$ be the function of
[Herbrand's functions](herbrand-functions.md). Let $H$ be a normal subgroup of $G$ and $K' \subseteq L$ its
fixed field, so that $G/H = \operatorname{Gal}(K'/K)$, a finite Galois extension of the same kind, with its
own function $i_{G/H}$, defined through the normalized valuation $v_{K'}$ of $K'$. Let
$e' = e_{L/K'}$ be the ramification index of $L/K'$. Then for every $\sigma \in G/H$

$$i_{G/H}(\sigma) = \frac{1}{e'} \sum_{s \mapsto \sigma} i_G(s),$$

the sum running over the elements $s \in G$ with image $\sigma$; both sides are $+\infty$ for $\sigma = 1$.

In particular, if $H = G_j$ for an integer $j \ge 0$, then $(G/H)_i = G_i/H$ for $i \le j$ and
$(G/H)_i = \{1\}$ for $i \ge j$.

The proof, after Tate, fixes generators $x$ of $\mathcal{O}_L$ and $y$ of $\mathcal{O}_{K'}$ as
$\mathcal{O}_K$-algebras and a representative $s \in G$ of $\sigma \ne 1$, and shows that
$a = s(y) - y$ and $b = \prod_{t \in H} (st(x) - x)$ generate the same ideal of $\mathcal{O}_L$: with $f$ the
minimal polynomial of $x$ over $K'$, $f(X) = \prod_{t \in H}(X - t(x))$ has coefficients in
$\mathcal{O}_{K'}$, $a$ divides $s(f)(x) = \pm b$, and writing $y = g(x)$ with $g \in \mathcal{O}_K[X]$ and
$g(X) - y = f(X) h(X)$ with $h \in \mathcal{O}_{K'}[X]$ gives $y - s(y) = s(f)(x) \cdot s(h)(x)$, so that $b$
divides $a$. Since $v_L$ restricts to $e' v_{K'}$ on $K'$, $e' \, i_{G/H}(\sigma) = v_L(a)$, while
$v_L(b) = \sum_{t \in H} i_G(st)$. The particular case follows because a $\sigma \ne 1$ lies in
$G_i/H \smallsetminus G_{i+1}/H$ for a unique $i < j$, its representatives $s$ have $i_G(s) = i + 1$, and $e'$
is the order of $H \subseteq G_0$.

## Depends on

- [Herbrand's functions](herbrand-functions.md), for the functions $i_G$ and $i_{G/H}$
- [Ramification groups of local fields](../ramification-groups-of-local-fields.md), for the groups $G_i$ and the ramification index

## Proof depends on

- [Monogenicity of extensions with separable residue field extension](../../../../RingTheory/ramification/monogenic-extensions-of-discrete-valuation-rings/exists-adjoin-eq-top-of-separable-residu.md), for the generators $x$ of $\mathcal{O}_L$ and $y$ of $\mathcal{O}_{K'}$ over $\mathcal{O}_K$; its hypotheses hold, these rings being finite over $\mathcal{O}_K$ with local structure maps and separable residue field extensions, the residue fields being perfect
- [Ramification groups of local fields](../ramification-groups-of-local-fields.md), for $G_0$ being the inertia group, of order $e_{L/K}$, so that $e' = \lvert H \rvert$ when $H \subseteq G_0$, used in the particular case

## Sources

- J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer, 1979, Chapter IV, §1:
  Proposition 3, p. 63 ("For every $\sigma \in G/H$, $i_{G/H}(\sigma) = \frac{1}{e'} \sum_{s \to \sigma} i_G(s)$,
  where $e' = e_{L/K'}$"), its proof "after J. Tate", pp. 63–64, and the Corollary to it, p. 64, with its
  proof; Serre assumes only that the residue extension is separable.
