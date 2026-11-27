# Men's join of two stable matchings

Let $M$ (the men) and $W$ (the women) be finite sets, every man with a strict total order of preference on $W$ and every woman with one on $M$. A perfect matching is a bijection $\mu : M \to W$; a pair $(m, w)$ blocks $\mu$ if $m$ prefers $w$ to $\mu(m)$ and $w$ prefers $m$ to $\mu^{-1}(w)$, and $\mu$ is stable if no pair blocks it.
For stable perfect matchings $\mu$ and $\nu$, the men's join $\mu \vee \nu$ is the perfect matching that
gives every man $m$ the partner he prefers among $\mu(m)$ and $\nu(m)$. It is a perfect matching because
this map is injective and the two sides have the same size.

## Informally uses

- [The men's join of two stable matchings is injective](men-join-fun-injective.md): no two men prefer the same woman, which uses the stability of $\mu$ and $\nu$.

## Sources

- A. E. Roth, "On the allocation of residents to rural hospitals: a general property of two-sided matching markets", *Econometrica* 54(2) (1986), 425–427, Lemma 2 (marriage case: every quota equals one and the choice set `Ch(x(h) ∪ y(h))` is the preferred of two partners).
