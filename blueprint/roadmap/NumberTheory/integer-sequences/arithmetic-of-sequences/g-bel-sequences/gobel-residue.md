# Residue sequence of the $k$-Göbel sequence

Fix natural numbers $k$, $p$, $r$ and write
$\nu_p$ for the $p$-adic valuation. The residue sequence $g_{k,p,r}(n)$, meant for $n \ge 1$ with
$\nu_p(n!) \le r$, takes values in $\mathbb{Z}/p^{r - \nu_p(n!)}\mathbb{Z} \cup \{F\}$, where $F$
is a failure value; a residue class is represented by its least nonnegative representative. It
is defined by $g_{k,p,r}(0) = F$, $g_{k,p,r}(1) = 2 \bmod p^r$ and, for $n \ge 2$, as follows.
If $g_{k,p,r}(n-1) = F$ then $g_{k,p,r}(n) = F$. Otherwise let $g_{k,p,r}(n-1) = a$ and let $N$
be the least nonnegative residue of $(n-1)a + a^k$ modulo $p^{r - \nu_p((n-1)!)}$, with $a^k$
computed by modular exponentiation. If $N \not\equiv 0 \pmod{p^{\nu_p(n)}}$ then
$g_{k,p,r}(n) = F$; otherwise $g_{k,p,r}(n) = (N/p^{\nu_p(n)}) \cdot c \bmod p^{r - \nu_p(n!)}$,
where $c$ is the inverse of the quotient $n/p^{\nu_p(n)}$ modulo $p^{r - \nu_p(n!)}$ (it exists
when $p$ is prime; when no inverse exists, $c$ is the junk value that Mathlib's inverse in
$\mathbb{Z}/p^{r - \nu_p(n!)}\mathbb{Z}$ returns, which need not be $0$).

For a prime $p$ with $\nu_p(n!) \le r$ we have $\nu_p(n) + (r - \nu_p(n!)) = r - \nu_p((n-1)!)$,
so the reduction keeps exactly the information both the divisibility test and the next residue
need, and the recursion agrees with the source's, which tests and divides $(n-1)a + a^k$ itself.
Values with $\nu_p(n!) > r$ and at $n = 0$ are junk and never used.

## Sources

- Yuh Kobayashi and Shin-ichiro Seki, *On the Length over Which k-Göbel Sequences Remain Integers*, INTEGERS 26 (2026), Article A23, Section 2 (definition of `g_{k,p,r}`, after Matsuhira, Matsusaka, and Tsuchida, Definition 9).
