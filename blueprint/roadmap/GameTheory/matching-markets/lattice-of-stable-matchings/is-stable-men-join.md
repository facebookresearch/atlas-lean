# The men's join of two stable matchings is stable

Let $M$ (the men) and $W$ (the women) be finite sets, every man with a strict total order of preference on $W$ and every woman with one on $M$. A perfect matching is a bijection $\mu : M \to W$; a pair $(m, w)$ blocks $\mu$ if $m$ prefers $w$ to $\mu(m)$ and $w$ prefers $m$ to $\mu^{-1}(w)$, and $\mu$ is stable if no pair blocks it.
If $\mu$ and $\nu$ are stable perfect matchings, the men's join $\mu \vee \nu$, which gives every man the
partner he prefers among $\mu(m)$ and $\nu(m)$, is stable.

Proof: if a man $m$ and a woman $w$ block the join, let $m'$ be her partner in the join, which is her partner
in $\mu$ or in $\nu$, say $\mu$. Then $m$ prefers $w$ to his join partner, hence to $\mu(m)$, and $w$ prefers
$m$ to $m'$, her $\mu$-partner, so $(m, w)$ blocks $\mu$.

This is the marriage case, with complete preference lists, of Roth (1986), Lemma 2, whose footnote
attributes the property to Conway via Knuth (1976) (a secondary attribution; Knuth's book was not
consulted).

## Informally uses

- [Preferred to the join, preferred to the first partner](lt-left-of-lt-men-join-fun.md): the blocking man prefers the woman to his partner in $\mu$.
- [Preferred to the join, preferred to the second partner](lt-right-of-lt-men-join-fun.md): and to his partner in $\nu$.

## Background

- [Men's join of two stable matchings](men-join.md): the matching whose stability is asserted.

## Sources

- A. E. Roth, "On the allocation of residents to rural hospitals: a general property of two-sided matching markets", *Econometrica* 54(2) (1986), 425–427, Lemma 2.
