# The rounding indicator $\delta$

Let $p$, $d$ and $i$ be natural numbers and let
$\tau = (p + 1)/d$. For a rational $x$ and an integer $k$, write $[p^k](x)$ for the residue of
$\lfloor x / p^k \rfloor$ modulo $p$, the $k$-th base-$p$ digit of $x$. Then $\delta(i) = 0$ if
the integer-part digits $([p^n](\tau i))_{n \ge 0}$ are lexicographically larger than the
fractional digits $([p^{-1-n}](\tau i))_{n \ge 0}$, that is, the two sequences agree at every
index below some $m$ and the first is larger at $m$; otherwise $\delta(i) = 1$.

## Sources

- Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Definition of `δ`.
