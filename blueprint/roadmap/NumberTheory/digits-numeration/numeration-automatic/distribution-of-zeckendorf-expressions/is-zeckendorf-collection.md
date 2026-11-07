# Zeckendorf collections

Index coefficient functions from $1$, let $\beta^n$ be the basis
coefficient function with entry $1$ at index $n$, and for a coefficient function $\mu$ let
$\operatorname{res}_n(\mu)$ keep the entries of $\mu$ at indices $\le n$ and
$\operatorname{res}^n(\mu)$ keep those at indices $\ge n$, the other entries being $0$. A set $E$
of finitely supported coefficient functions $\mathbb N \to \mathbb N$ is a Zeckendorf collection
when it contains $0$ and $\beta^n$ for every $n \ge 1$, every $\mu \in E$ has only finitely many
elements of $E$ below it in the ascending lexicographic order $\lt _a$, and for every $\mu \in E$
and every immediate successor $\tilde\mu$ of $\mu$ in $E$ with $\tilde\mu \ne \beta^1 + \mu$
there is an index $n \ge 2$ such that $\operatorname{res}_{n-1}(\mu)$ is the immediate
predecessor of $\beta^n$ in $E$ and $\tilde\mu = \beta^n + \operatorname{res}^n(\mu)$.

## Sources

- Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25, Section 2 (arXiv:2308.12872v1, Section 2.2).
