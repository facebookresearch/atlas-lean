# The lattice boundary $\mu$

Let $p$, $d$ and $i$ be natural numbers and let
$\tau = (p + 1)/d$, taken to be $0$ when $d = 0$. For a rational $x$ and an integer $k$, write
$[p^k](x)$ for the residue of $\lfloor x/p^k \rfloor$ modulo $p$, the $k$-th base-$p$ digit
of $x$. Then $\mu(i)$ is $\lfloor \tau i \rfloor$ if the integer-part digit sequence
$([p^n](\tau i))_{n \ge 0}$ is lexicographically larger than the fractional digit sequence
$([p^{-1-n}](\tau i))_{n \ge 0}$, that is, the two sequences agree at every index below some
$m$ and the first is larger at $m$; otherwise $\mu(i) = \lceil \tau i \rceil$.

## Sources

- Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Definition 1 (`μ`).
