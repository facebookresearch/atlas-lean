# Weak maximum principle for subharmonic functions

Let $U$ be a nonempty bounded open subset of a nontrivial finite-dimensional real inner product
space, for instance of $\mathbb{R}^n$ with $n \ge 1$. Let $u$ be continuous on $\overline U$ and
$C^2$ on $U$ with $\Delta u \ge 0$ on $U$. Then $u$ attains its maximum over $\overline U$ at a
point of $\partial U$:

$$\max_{\overline U} u = \max_{\partial U} u.$$

**Proof idea.** For $\varepsilon > 0$ the function $v = u + \varepsilon \|x\|^2$ satisfies
$\Delta v = \Delta u + 2 n \varepsilon > 0$ on $U$, so it has no maximum in $U$; if $u$ exceeded its
boundary maximum somewhere, a small $\varepsilon$ would produce one.

This is Theorem 3.13 of Schmidt's notes for the operator $L = \Delta$ (stated there for general
elliptic $L u \ge 0$ with coefficients continuous up to the boundary), and contains the weak
maximum principle for harmonic functions. Nontriviality of the space excludes dimension $0$, where
the one-point space is a bounded open set with empty boundary.

## Informally uses

- [The Laplacian is nonpositive at an interior maximum](laplacian-nonpos-of-is-local-max.md): the
  contradiction at an interior maximum of $v$.
- [Laplacian of the squared norm](laplacian-norm-sq.md): $\Delta v = \Delta u + 2 n \varepsilon$.

## Background

- [Subharmonic functions](../subharmonic-functions/README.md): subharmonicity defined by the
  sub-mean-value property; for $C^2$ functions it amounts to $\Delta u \ge 0$, the hypothesis here.

## Sources

- M. Schmidt, *Partial Differential Equations*, lecture notes, Universität Mannheim, HWS 2025, [Chapter 3 (Laplace equation)](https://www.wim.uni-mannheim.de/media/Lehrstuehle/wim/schmidt/HWS2025/chapter_3.pdf), Theorem 3.13.
- L. C. Evans, *Entropy and Partial Differential Equations*, lecture notes, [entropy.and.PDE.pdf](https://math.berkeley.edu/~evans/entropy.and.PDE.pdf), Chapter IV.A.3: the weak maximum principle for $-\sum (a^{ij} u_{x_i})_{x_j} = 0$, proved by
  testing against $u^-$, in the proof of the Corollary (strong maximum principle).
- L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS Graduate Studies in Mathematics 19 (2010), Chapter 2. Not consulted directly; no theorem number is cited from it.
