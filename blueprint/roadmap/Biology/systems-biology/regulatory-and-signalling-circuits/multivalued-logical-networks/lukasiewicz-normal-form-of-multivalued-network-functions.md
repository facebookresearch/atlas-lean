# Łukasiewicz normal form of multivalued network functions

**Setting.** Fix $m\ge1$ and $X_m=\{0,\tfrac1m,\dots,\tfrac{m-1}m,1\}$. On $X_m$ define

$$\neg x=1-x,\qquad x\oplus y=\min\{1,x+y\},\qquad x\odot y=\max\{0,x+y-1\},$$

which satisfy the De Morgan laws $x\odot y=\neg(\neg x\oplus\neg y)$; $\oplus,\odot$ are associative and commutative and $\bigodot_{k=1}^r a_k=\max\{0,\sum_ka_k-(r-1)\}$ (Proposition 4). For $m=1$ these are Boolean OR and AND.

**Theorem 11 (functional completeness).** Every function $f:X_m^n\to X_m$ is expressible in terms of $\odot$, $\neg$ and constant functions.

**$\odot$-$\neg$ functions.** $f$ is a $\odot$-$\neg$ function if $f(x)=\bigodot_{j\in A}x_j^{p_j}\odot\bigodot_{j\in B}\neg(x_j)^{q_j}\odot\frac cm$ with $c\in\{0,\dots,m\}$ and $p_j,q_j\in\mathbb N$ (powers are iterated $\odot$). Its signed, weighted wiring diagram has an edge $x_j\to x_k$ of weight $p$, an inhibitory edge of weight $q$, and an edge from a constant node of weight $c/m$; the diagram determines the function and conversely.

**Theorem 20 (canonical form).** A $\odot$-$\neg$ function is either $\equiv0$ or can be written with disjoint $A,B$ and exponents capped at $c$:

$$f(x)=\bigodot_{j\in A}x_j^{\min\{p_j,c\}}\odot\bigodot_{j\in B}\neg(x_j)^{\min\{q_j,c\}}\odot\frac cm,$$

and this expression is unique; the bound $c$ on exponents is sharp (Proposition 19).

**Theorem 26 (reduction).** Every network $F:X_m^{n_1}\to X_m^{n_1}$ can be extended by at most $\mu(F)$ auxiliary variables $U$ to a network $\overline F:X_m^{n_2}\to X_m^{n_2}$ consisting of $\odot$-$\neg$ functions, with $\pi\circ\overline F\circ(\mathrm{Id},U)=F$, and the fixed points of $F$ correspond bijectively to those of $\overline F$ by projection to the first $n_1$ coordinates.

## Expansion

Functional completeness mirrors the Boolean disjunctive normal form: indicator functions of single points of $X_m$ can be built from $\odot$, $\neg$ and constants (powers $x^{k}=\max\{0,kx-(k-1)\}$ act as sharpening thresholds), and $\oplus$ is obtained from $\odot$ and $\neg$ by De Morgan. In the canonical form, a $\odot$ product of literals equals $\max\{0,\sum_jp_jx_j+\sum_jq_j(1-x_j)+\frac cm-\sum_jp_j-\sum_jq_j\}$; an exponent above $c$ can never change whether this is positive, so capping at $c$ loses nothing, and different capped data give different functions. The reduction introduces one new variable for each non-$\odot$-$\neg$ subexpression, defined recursively so that it agrees with that subexpression at fixed points.

## Sources

- J. García Galofre, M. Pérez Millán, A. Galarza Rial, R. Laubenbacher, "Beyond Boolean networks: new tools for the steady state analysis of multivalued networks", *SIAM Journal on Applied Dynamical Systems* 25(1) (2026), 77–107, Proposition 4, Theorem 11, Proposition 19, Theorem 20 and Theorem 26, <https://doi.org/10.1137/24m1657249> (preprint arXiv:2404.16760).
