# Fuel-bounded generalized Hofstadter recursion

For natural numbers $k$, $p$ and $n$, the
value $A_k(p, n)$ is defined by recursion on the fuel $p$, which bounds the recursion depth:
$A_k(0, n) = 0$ and $A_k(p + 1, n) = n - g^k(n - 1)$, where $g^k$ is the $k$-fold iterate of the
function $g(m) = A_k(p, m)$ and both subtractions are truncated at $0$.

## Sources

- Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3, Section 1.4 (Rocq definition `recf`).
