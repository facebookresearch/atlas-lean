# Bounded order of semisimple subgroups of GL₂(F_ℓ) with few characteristic polynomials

Let $\eta$ and $M$ be nonnegative real numbers. A subgroup $G$ of $\mathrm{GL}_2(\mathbb{F}_\ell)$, for a prime $\ell$,
satisfies the condition $C(\eta, M)$ if there is a subset $H$ of $G$ with $|H| \ge (1 - \eta)\,|G|$ such that the set of
polynomials $\det(1 - hT)$, $h \in H$, has at most $M$ elements; here $|X|$ is the cardinality of a finite set $X$.

Let $\eta < 1/2$ and $M \ge 0$. There is a constant $A = A(\eta, M)$ such that for every prime $\ell$ and every
[semisimple subgroup](semisimple-subgroups-of-gl2-over-a-prime-field.md) $G$ of $\mathrm{GL}_2(\mathbb{F}_\ell)$ satisfying
$C(\eta, M)$,

$$|G| \le A.$$

Proof (Deligne–Serre, p. 524). By the
[classification of semisimple subgroups](semisimple-subgroups-of-gl2-over-a-prime-field.md), $G$ falls in one of four
cases.

- (a) $G \supseteq \mathrm{SL}_2(\mathbb{F}_\ell)$. With $r = (G : \mathrm{SL}_2(\mathbb{F}_\ell))$, $|G| = r\ell(\ell^2 - 1)$. The number of
  elements of $\mathrm{GL}_2(\mathbb{F}_\ell)$ with a given characteristic polynomial is $\ell^2 + \ell$, $\ell^2$ or $\ell^2 - \ell$
  according as the polynomial has $2$, $1$ or $0$ roots in $\mathbb{F}_\ell$. So $C(\eta, M)$ gives

    $$(1 - \eta)\, r\ell(\ell^2 - 1) = (1 - \eta)\,|G| \le |H| \le M(\ell^2 + \ell),$$

    hence $(1 - \eta) r(\ell - 1) \le M$ and $\ell \le 1 + M/((1 - \eta) r) \le 1 + M/(1 - \eta)$, which bounds $\ell$ and so
    $|G| \le |\mathrm{GL}_2(\mathbb{F}_\ell)|$.
- (b) $G \subseteq T$, a Cartan subgroup. At most $2$ elements of $T$ have a given characteristic polynomial, so
  $(1 - \eta)|G| \le 2M$ and $|G| \le 2M/(1 - \eta)$.
- (c) $G$ lies in the normalizer of a Cartan subgroup $T$ but not in $T$. Then $G' = G \cap T$ has index $2$ in $G$ when
  $\ell$ is odd (for $\ell = 2$, $|G| \le |\mathrm{GL}_2(\mathbb{F}_2)| = 6$); if $G$ satisfies $C(\eta, M)$, $G'$ satisfies
  $C(2\eta, M)$, and (b) applied to $G'$ gives $|G| \le 4M/(1 - 2\eta)$.
- (d) The image of $G$ in $\mathrm{PGL}_2(\mathbb{F}_\ell)$ has order at most $60$, so $G \cap \mathrm{SL}_2(\mathbb{F}_\ell)$, whose
  elements with the same image differ by $\pm 1$, has order at most $120$; at most $120$ elements of $G$ have a given
  determinant, a fortiori a given characteristic polynomial, so $(1 - \eta)|G| \le 120M$ and $|G| \le 120M/(1 - \eta)$.

The remark on $\ell = 2$ in (c) is added here: Deligne and Serre state the index $2$ without restriction.

## Depends on

- [Semisimple subgroups of GL₂ over a prime field](semisimple-subgroups-of-gl2-over-a-prime-field.md), for the definition of a semisimple subgroup of $\mathrm{GL}_2(\mathbb{F}_\ell)$

## Proof depends on

- [Semisimple subgroups of GL₂ over a prime field](semisimple-subgroups-of-gl2-over-a-prime-field.md), for the four cases

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): §7.1 and the condition $C(\eta, M)$, p. 523
  ("Il existe une partie H de G telle que |H| ≧ (1 − η)|G|, et que l'ensemble des polynômes det(1 − hT), h ∈ H, ait au
  plus M éléments"); Proposition 7.2 and its proof, cases (a)–(d), p. 524 ("Soient η < 1/2 et M ≧ 0. Il existe une
  constante A = A(η, M) telle que, pour tout nombre premier l, et tout sous-groupe semi-simple G de
  $\mathbf{GL}_2(\mathbf{F}_l)$ satisfaisant à C(η, M), on ait |G| ≦ A").
