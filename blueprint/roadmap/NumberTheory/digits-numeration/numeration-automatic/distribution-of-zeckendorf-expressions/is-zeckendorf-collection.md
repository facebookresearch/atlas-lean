# Zeckendorf collections

In Chang's one-based indexing, let $\beta^n$ be the basis
coefficient function with entry $1$ at index $n$, and for a coefficient function $\mu$ let
$\operatorname{res}_n(\mu)$ keep the entries of $\mu$ at indices $\le n$ and
$\operatorname{res}^n(\mu)$ keep those at indices $\ge n$, the other entries being $0$. A set $E$
of finitely supported coefficient functions $\mathbb N \to \mathbb N$ is a Zeckendorf collection
when it contains $0$ and $\beta^n$ for every $n \ge 1$, every $\mu \in E$ has only finitely many
elements of $E$ below it in the ascending lexicographic order $\lt _a$, and for every $\mu \in E$
and every immediate successor $\tilde\mu$ of $\mu$ in $E$ with $\tilde\mu \ne \beta^1 + \mu$
there is an index $n \ge 2$ such that $\operatorname{res}_{n-1}(\mu)$ is the immediate
predecessor of $\beta^n$ in $E$ and $\tilde\mu = \beta^n + \operatorname{res}^n(\mu)$.

Lean represents Chang's basis digit $\beta^n$ by `Finsupp.single (n - 1) 1` for $n \ge 1$.
The first basis digit is `Finsupp.single 0 1`, and a carry at Chang's index $n \ge 2$ occurs
at Lean index $m = n - 1 \ge 1$.

## Sources

- Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25, Section 2 (arXiv:2308.12872v1, Section 2.2).
