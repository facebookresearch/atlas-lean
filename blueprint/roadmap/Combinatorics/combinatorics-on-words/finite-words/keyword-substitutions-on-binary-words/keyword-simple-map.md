# Simple map

Let $a$ be a keyword, a binary word of length $m + 1$, and let
$i \in \mathbb{N}$. The simple map $\varphi_i$ sends a binary word $u$ of length $n$ to the word
obtained by negating the letters of $u$ at positions $i, \dots, i + m$ (positions counted from
$0$) if $a$ is applicable to $u$ at letter $i$, that is, if $i + m < n$ and the subword of $u$ at
positions $i, \dots, i + m$ equals $a$ or its letterwise negation $\neg a$; otherwise
$\varphi_i(u) = u$.

The paper counts letters from $1$, so its simple map $\varphi_i$ is $\varphi_{i-1}$ in this
numbering.

## Sources

- Erik Bates, Blan Morrison, Mason Rogers, Arianna Serafini and Anav Sood, *A New Combinatorial Interpretation of Partial Sums of m-Step Fibonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.6.6, Section 2.1 (simple maps).
