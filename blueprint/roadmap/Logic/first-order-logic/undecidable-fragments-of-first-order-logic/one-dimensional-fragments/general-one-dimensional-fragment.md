# General one-dimensional fragment of first-order logic

The general one-dimensional fragment $\mathrm{GF}_1$ consists of the first-order formulas built from unary atoms by Booleans and by existential quantification of blocks of variables that leaves at most one variable free, the quantified matrix being a Boolean combination of atoms and of $\mathrm{GF}_1$ formulas.

Fix a relational vocabulary $\tau$. The set of $\tau$-formulas of $\mathrm{GF}_1$ is the smallest set $\mathcal{F}$ such that:

1. every unary $\tau$-atom is in $\mathcal{F}$, and $\top, \bot \in \mathcal{F}$;
2. $\mathcal{F}$ is closed under $\neg$ and $\wedge$;
3. if $Y = \{y_1, \dots, y_k\}$ is a set of variables, $U$ a finite set of formulas of $\mathcal{F}$ with free variables in $Y$, $F$ a set of $\tau$-atoms with variables in $Y$, and $\varphi$ a Boolean combination of formulas in $F \cup U$, then $\exists y_2 \cdots \exists y_k\, \varphi \in \mathcal{F}$ and $\exists y_1 \cdots \exists y_k\, \varphi \in \mathcal{F}$.

Thus every formula of $\mathrm{GF}_1$ has at most one free variable. The *uniform one-dimensional fragment* $\mathrm{UF}_1$ is defined in the same way but additionally requires the atoms of arity at least two in $F$ to use exactly the same set of variables (uniformity); $\mathrm{UF}_1$ has a decidable satisfiability problem, which $\mathrm{GF}_1$ does not.

## Depends on

None.

## Proof depends on

None.

## Expansion

$\mathrm{UF}_1$ contains the two-variable fragment of first-order logic and the polyadic modal logics with Boolean combinations of accessibility relations; $\mathrm{GF}_1$ drops the uniformity condition and so can relate a variable to several others by different binary atoms in one quantified block, which is what tilings need.

## Sources

- L. Hella and A. Kuusisto, "One-dimensional fragment of first-order logic", in *Advances in Modal Logic 10 (AiML 2014)*, College Publications, 2014, pp. 274–293; read as arXiv:1404.4004v1, <https://arxiv.org/abs/1404.4004v1>: the definition of $\mathrm{GF}_1$ in Section 5 and of $\mathrm{UF}_1$ in Section 3, and the decidability of $\mathrm{UF}_1$ (Section 4).
