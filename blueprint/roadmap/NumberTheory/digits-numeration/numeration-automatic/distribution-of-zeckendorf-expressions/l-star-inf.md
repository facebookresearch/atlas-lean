# The coefficient function $\inf(\varepsilon)$

Let $L$ be a list of natural numbers and
$\varepsilon : \mathbb{N} \to \mathbb{N}$ a coefficient function, with indices starting at $0$.
If $\varepsilon$ has a last nonzero entry, at index $c$, then $\inf(\varepsilon)$ agrees with
$\varepsilon$ at the indices $i < c$, equals $\varepsilon_c - 1$ at $c$, and agrees with the
maximal $L^*$-block starting at index $c + 1$ at the indices $i > c$. Otherwise, that is, when
$\varepsilon$ has infinite support or is zero, $\inf(\varepsilon) = \varepsilon$.

In the paper's one-based indexing the last nonzero entry sits at index $c + 1$, and
$\inf(\varepsilon) = \operatorname{res}_{c+1}(\varepsilon) - \beta^{c+1} + \bar\beta^{c+2}$,
where $\operatorname{res}_{c+1}(\varepsilon)$ keeps the entries of $\varepsilon$ at the indices
at most $c + 1$, $\beta^{c+1}$ has a single entry $1$ at index $c + 1$ and zeros elsewhere, and
$\bar\beta^{c+2}$ is the maximal $L^*$-block starting at index $c + 2$ (all in paper indices).

## Sources

- Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25, Section 2 (arXiv:2308.12872v1, Section 2.3).
