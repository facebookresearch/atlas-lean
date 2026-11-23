# Fundamental domain for a subgroup of countable index

Let a group $G$ act measurably on a measurable space $X$ preserving a measure $\mu$, let
$\Gamma_2 \le \Gamma_1 \le G$ with $\Gamma_1$ countable, and let $\mathcal F$ be a fundamental domain
for $\Gamma_1$. If $(R_i)_{i \in I}$, with $I$ countable, are elements of $\Gamma_1$ such that every
$\gamma \in \Gamma_1$ has exactly one $i$ with $R_i^{-1} \gamma \in \Gamma_2$, representatives of the
left cosets of $\Gamma_2$ in $\Gamma_1$, then $\bigcup_i R_i^{-1} \mathcal F$ is a fundamental domain
for $\Gamma_2$.

## Idea

A smaller group needs a larger fundamental domain. Fundamental domains are meant up to null sets:
the translates of $\mathcal F$ by $\Gamma_1$ cover $X$ up to a null set and any two of them meet
in a null set. As $\Gamma_1$ is the disjoint union of the cosets $R_i \Gamma_2$, the products
$\gamma R_i^{-1}$ with $\gamma \in \Gamma_2$ run through $\Gamma_1$, each element once, so the
$\Gamma_2$-translates of $\bigcup_i R_i^{-1} \mathcal F$ are made of the $\Gamma_1$-translates of
$\mathcal F$, each used once: they cover $X$ up to a null set, and, $\Gamma_1$ being countable, any
two of them meet in a null set. For $2\mathbb{Z} \le \mathbb{Z}$ acting on $\mathbb{R}$ by
translation, the representatives $0$ and $-1$ turn the fundamental domain $[0, 1)$ of $\mathbb{Z}$
into $[0, 2)$. Integrals over the new domain are then integrals over $\mathcal F$ of sums over the
cosets, as the second statement records.

## Statements

- [Fundamental domain for a subgroup of countable index](i-union-inv-smul-of-left-coset-represent.md)
- [Integrals over a subgroup fundamental domain as sums over cosets](set-lintegral-i-union-inv-smul-eq-and-se.md): integrals over that domain as sums over the cosets.
