# Stable matching with singles

Let $M$ (the men) and $W$ (the women) be sets; each man has a strict total order of preference on $W \cup \{\varnothing\}$ and each woman one on $M \cup \{\varnothing\}$, where $\varnothing$ stands for remaining single. A matching with singles is a partial bijection $\mu$ between $M$ and $W$: $\mu(m) \in W \cup \{\varnothing\}$ is the partner of man $m$ and $\mu^{-1}(w) \in M \cup \{\varnothing\}$ that of woman $w$, with $\varnothing$ meaning single.
A matching with singles $\mu$ is stable when

- no man prefers remaining single to his assignment $\mu(m)$, and no woman prefers remaining single to her
  assignment $\mu^{-1}(w)$ (individual rationality), and
- no man $m$ and woman $w$ both prefer each other to their assignments: it is not the case that $m$
  prefers $w$ to $\mu(m)$ and $w$ prefers $m$ to $\mu^{-1}(w)$.

A pair already matched to each other never satisfies the second condition, since nobody strictly prefers a
partner to the same partner, so the condition "not matched to each other" in the source is automatic.

## Sources

- A. E. Roth, "On the allocation of residents to rural hospitals: a general property of two-sided matching markets", *Econometrica* 54(2) (1986), 425–427, p. 426 (the definitions of an individually rational and of an unstable outcome, with every quota equal to one).
