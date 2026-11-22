# Weak maximum principle for the heat equation

Let $U$ be a nonempty bounded open subset of a finite-dimensional real inner product space and
$T \ge 0$. Let $u$ be continuous on $[0, T] \times \overline U$, with $u(t, \cdot)$ of class $C^2$
on $U$ and $s \mapsto u(s, x)$ left-differentiable with derivative $u_t(t, x)$, for $t \in (0, T]$
and $x \in U$. If $u_t - \Delta u \le 0$ on $(0, T] \times U$, then $u$ attains its maximum over
$[0, T] \times \overline U$ at a point of the parabolic boundary.

Schmidt states the principle for solutions of the heat equation; this version holds for
subsolutions and needs only one-sided time derivatives, which is what the top face $t = T$ of the
cylinder provides.

**Proof idea.** The function $v = u - \varepsilon t$ satisfies $v_t - \Delta v \le -\varepsilon$.
At a maximum of $v$ off the parabolic boundary, the Laplacian is nonpositive and the left time
derivative is nonnegative, a contradiction.

## Informally uses

- [The Laplacian is nonpositive at an interior maximum](../../potential-theory/maximum-principle-for-harmonic-functions/laplacian-nonpos-of-is-local-max.md):
  the spatial half of the contradiction.

## Background

- [Parabolic boundary of a space-time cylinder](parabolic-boundary.md): where the maximum lies.

## Sources

- M. Schmidt, *Partial Differential Equations*, lecture notes, Universität Mannheim, HWS 2025, [Chapter 4 (Heat equation)](https://www.wim.uni-mannheim.de/media/Lehrstuehle/wim/schmidt/HWS2025/chapter_4.pdf), Theorem 4.9.
- L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS Graduate Studies in Mathematics 19 (2010), Chapter 2. Not consulted directly; no theorem number is cited from it.
