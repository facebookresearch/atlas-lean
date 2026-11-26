# Generating function of $m$-regular linear stacks

**Setting.** A *stack* on $[n]=\{1,\dots,n\}$ is a noncrossing diagram (arcs drawn above the line, no loops or multiple arcs); stacks and queues are the building blocks into which protein contact maps decompose. A stack is **$m$-regular** if every arc $(i,j)$ has length $j-i\ge m$ and **linear** if every vertex has degree at most $2$. RNA secondary structures are $2$-regular stacks of maximum degree $1$; *extended* RNA secondary structures, in which a base may pair twice, are exactly the $2$-regular linear stacks. A **zigzag stack** is a noncrossing diagram of maximum degree $2$ in which the two arcs at any degree-$2$ vertex lie on the same side of it.

Let $r_m(n)$ count $m$-regular linear stacks on $[n]$, $R_m(x)=\sum_{n\ge0}r_m(n)x^n$ with $r_m(0)=1$, and let $Z(x)=\sum_n z(n)x^n$ count zigzag stacks.

**Theorem.**

*(1)* *(Zigzag stacks.)* $x^2(x-1)Z^3(x)+2xZ^2(x)-(x+1)Z(x)+1=0$, and $z(n)\sim 0.4781905\times4.6107186^n\,n^{-3/2}$.

*(2)* *(Reduction.)* If $Z_m$ counts $m$-reduced zigzag stacks, then $z_m(n)=r_m(n+m-1)$, i.e. $R_m(x)=1+x+\dots+x^{m-2}+x^{m-1}Z_m(x)$.

*(3)* *(Main equation.)* For every $m\ge2$, $R_m$ satisfies the quintic

$$\sum_{j=0}^{5}c_j(x)R_m^j=0,$$

with $c_0=(x-1)(x^m-1)^3$, $c_1=(x^m-1)^2(x^{2m+1}-2x^{m+2}-x^{m+1}+x^m-3x^3+8x^2-3x-1)$, $c_2=-x(x-1)(x^m-1)(5x^{2m+1}-6x^{m+2}-9x^{m+1}+5x^m-3x^3+12x^2+x-5)$, $c_3=x^2(x-1)^2(x^m-1)(11x^{m+1}-8x^2-11x+8)$, $c_4=x^3(x-1)^3(-11x^{m+1}+4x^2+11x-4)$, $c_5=4x^5(x-1)^4$.

*(4)* *(Asymptotics.)* For fixed $m$, $r_m(n)\sim\gamma_m\,\omega_m^n\,n^{-3/2}$; for $m=2$ this recovers $r_2(n)\sim0.250536155\times4.1012475^n\,n^{-3/2}$ for extended RNA secondary structures, and e.g. $r_3(n)\sim0.19005341\times3.5271506^n\,n^{-3/2}$.

## Expansion

The Chen–Deng–Du reduction shortens every arc by $m-1$ in a way that is bijective onto $m$-reduced zigzag stacks, explaining the shift $z_m(n)=r_m(n+m-1)$. Zigzag stacks are enumerated by the primary component decomposition: the connected component containing vertex $1$ splits $[n]$ into intervals carrying smaller structures, which turns into an algebraic equation for the generating function; the $m$-reduced condition forbids certain substructures, adding the $x^m$ terms. Algebraicity of $R_m$ gives a linear recurrence with polynomial coefficients, and the square-root singularity found by Newton–Puiseux expansion gives the universal $n^{-3/2}$ factor.

## Sources

- William Y. C. Chen, Qiang-Hui Guo, Lisa H. Sun and Jian Wang, "Zigzag Stacks and m-Regular Linear Stacks", arXiv:1406.0947 (2014), Theorems 1.5, 2.1 and 2.2, the reduction relation between $R_m$ and $Z_m$ in Section 1, and Section 4, <https://doi.org/10.48550/arXiv.1406.0947>.
