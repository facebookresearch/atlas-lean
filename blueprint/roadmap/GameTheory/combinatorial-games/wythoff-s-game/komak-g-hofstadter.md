# Hofstadter recursion for the Komak sequence

Let $h$ be Hofstadter's $G$-sequence
(OEIS A005206), given by $h(0) = 0$ and $h(n) = n - h(h(n - 1))$ for $n \ge 1$. The sequence
$g$ of Komak et al. satisfies $g(0) = 1$, $g(1) = 0$, and for every $n \ge 2$,
$g(n) = 1 - g(h(n - 1))$ if $h(n - 2) < h(n - 1)$, and $g(n) = 1$ otherwise.

The source prints $g(1) = 1$. With $\varphi$ the golden ratio, $\lfloor \varphi \rfloor = 1 =
\lfloor 0 \cdot \varphi^2 \rfloor + 1$, so the definition of $g$ gives $g(1) = 1 - g(0) = 0$,
as in the source's table of values; the value is corrected to $g(1) = 0$.

## Sources

- Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6, Proposition 4 (`jis-2026-26.1.6-prop-4`).
