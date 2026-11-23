# The men's join of two stable matchings is injective

Let $M$ (the men) and $W$ (the women) be sets, every man with a strict total order of preference on $W$ and every woman with one on $M$. A perfect matching is a bijection $\mu : M \to W$; a pair $(m, w)$ blocks $\mu$ if $m$ prefers $w$ to $\mu(m)$ and $w$ prefers $m$ to $\mu^{-1}(w)$, and $\mu$ is stable if no pair blocks it. For perfect matchings $\mu$ and $\nu$, write $(\mu \vee \nu)(m)$ for the partner man $m$ prefers among $\mu(m)$ and $\nu(m)$.
If $\mu$ and $\nu$ are stable, the map $m \mapsto (\mu \vee \nu)(m)$ is injective: no two distinct men
prefer the same woman among their two partners.

Proof: if $m_1 \neq m_2$ both receive $w$, with $w = \mu(m_1) = \nu(m_2)$, then $m_1$ strictly prefers $w$ to
$\nu(m_1)$ and $m_2$ strictly prefers $w$ to $\mu(m_2)$. If $w$ prefers $m_1$ to $m_2$ then $(m_1, w)$ blocks
$\nu$; otherwise $(m_2, w)$ blocks $\mu$.

## Sources

- A. E. Roth, "On the allocation of residents to rural hospitals: a general property of two-sided matching markets", *Econometrica* 54(2) (1986), 425–427, Lemma 2 (feasibility of `w`, marriage case).
