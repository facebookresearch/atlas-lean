# The Komak sequence $g$

Let $\varphi$ be the golden ratio. The sequence
$g : \mathbb{N} \to \mathbb{N}$ of Komak et al. is defined by recursion on $n$: if some
$m < n$ satisfies $\lfloor n\varphi \rfloor = \lfloor m\varphi^2 \rfloor + 1$, then
$g(n) = 1 - g(m)$ for the least such $m$; otherwise $g(n) = 1$.

Such an $m$ is unique when it exists, and every $m$ with
$\lfloor n\varphi \rfloor = \lfloor m\varphi^2 \rfloor + 1$ satisfies $m < n$, so this agrees
with the source's definition, which does not restrict $m$ (there $\varphi^2$ is written
$\varphi + 1$). In particular $g(0) = 1$ and $g(1) = 0$.

## Sources

- Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6, Definition `def:fg` (arXiv:2512.11601v1).
