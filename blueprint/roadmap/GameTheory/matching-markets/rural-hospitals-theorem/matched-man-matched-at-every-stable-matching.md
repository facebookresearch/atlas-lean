# A man matched at one stable matching is matched at every stable matching

Let $M$ (the men) and $W$ (the women) be finite sets; each man has a strict total order of preference on $W \cup \{\varnothing\}$ and each woman one on $M \cup \{\varnothing\}$, where $\varnothing$ stands for remaining single. A matching with singles is a partial bijection $\mu$ between $M$ and $W$: $\mu(m) \in W \cup \{\varnothing\}$ is the partner of man $m$ and $\mu^{-1}(w) \in M \cup \{\varnothing\}$ that of woman $w$, with $\varnothing$ meaning single.
Let $\mu$ and $\nu$ be stable matchings with singles. A man who has a partner in $\mu$ has a partner in $\nu$.

Proof (a counting argument, not Roth's, who cites the result). Let $A$ be the men who prefer their
$\mu$-partner to their $\nu$-partner and $B$ the women who prefer their $\nu$-partner to their
$\mu$-partner. Stability of $\nu$ sends every man of $A$ to his $\mu$-partner, a woman of $B$; stability of
$\mu$ sends every woman of $B$ to her $\nu$-partner, a man of $A$. Both maps are injective, so
$|A| \le |B|$. If $m$ is matched in $\mu$ and single in $\nu$, then $m \in A$ by individual rationality, but
$m$ is nobody's $\nu$-partner, so the second map lands in $A \setminus \{m\}$, and $|B| < |A|$: a
contradiction.

## Background

- [Stable matching with singles](is-stable-single.md): individual rationality and the absence of blocking pairs, used for both matchings.

## Sources

- A. E. Roth, "On the allocation of residents to rural hospitals: a general property of two-sided matching markets", *Econometrica* 54(2) (1986), 425–427, Lemma 1 (marriage case: every quota equal to one).
