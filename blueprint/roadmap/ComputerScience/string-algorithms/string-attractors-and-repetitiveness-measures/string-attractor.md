# String attractors

Let $T = T[1..n]$ be a string over an alphabet $\Sigma$. A set $\Gamma \subseteq \{1, \dots, n\}$ is a *string attractor* of $T$ if every substring $T[i..j]$ has an occurrence $T[i'..j'] = T[i..j]$ that crosses some position of $\Gamma$, i.e. $i' \le k \le j'$ for some $k \in \Gamma$. The size of a smallest string attractor is denoted $\gamma(T)$. Every string of length $n \ge 1$ has $1 \le \gamma(T) \le n$, and $\gamma(T) \ge |\{\text{distinct letters of } T\}|$.

## Sources

- Dominik Kempa, Nicola Prezza, "At the Roots of Dictionary Compression: String Attractors", STOC (2018), arXiv:1710.10964.
