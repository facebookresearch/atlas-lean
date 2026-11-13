# Deleting the first occurrence of a letter

Let $w = \ell_0 \ell_1 \ell_2 \cdots$ be an
infinite word over the letters $a$ and $b$, let $\alpha$ be a letter, and let $p$ be the position
(counted from $0$) of the first occurrence of $\alpha$ in $w$, with $p = 0$ if $\alpha$ does not
occur in $w$. The word $D_\alpha(w)$ has letter $\ell_i$ at each position $i < p$ and letter
$\ell_{i+1}$ at each position $i \ge p$. So $D_\alpha(w)$ is $w$ with its first $\alpha$ deleted,
and, when $\alpha$ does not occur in $w$, it is $w$ with its first letter deleted.

## Sources

- Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Section 2 (definition of the deletion operators `D_a`, `D_b`).
