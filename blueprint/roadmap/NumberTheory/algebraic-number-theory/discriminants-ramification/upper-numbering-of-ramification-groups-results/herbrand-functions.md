# Herbrand's functions

Let $L/K$ be a finite Galois extension of complete discretely valued fields whose residue fields are perfect
of characteristic $p > 0$, with group $G = \operatorname{Gal}(L/K)$, normalized valuation $v_L$ of $L$ and
ramification groups $G_i$ ($i \ge -1$ an integer) in the lower numbering, as in
[Ramification groups of local fields](../ramification-groups-of-local-fields.md). Serre works more generally
with a complete discretely valued field $K$ and a finite Galois extension whose residue extension is
separable; this page states the case of perfect residue fields of positive characteristic.

For $s \in G$ put

$$i_G(s) = \inf_{a \in \mathcal{O}_L} v_L\bigl(s(a) - a\bigr) \in \mathbb{Z}_{\ge 0} \cup \{+\infty\},$$

so that $i_G(1) = +\infty$ and $s \in G_i$ if and only if $i_G(s) \ge i + 1$. For a real number $u \ge -1$ let
$G_u = G_i$, where $i$ is the smallest integer $\ge u$; thus $s \in G_u$ if and only if $i_G(s) \ge u + 1$.
**Herbrand's function** of $L/K$ is

$$\varphi_{L/K}(u) = \int_0^u \frac{dt}{(G_0 : G_t)} \qquad (u \ge -1),$$

where $(G_0 : G_t)$ is read as $(G_{-1} : G_0)^{-1}$ for $t = -1$ and as $1$ for $-1 < t \le 0$, so that
$\varphi_{L/K}(u) = u$ for $-1 \le u \le 0$. Write $g_i$ for the order of $G_i$.

1. The function $\varphi_{L/K}$ is continuous, piecewise linear, increasing and concave, and
   $\varphi_{L/K}(0) = 0$. Its right derivative $\varphi'_d$, at every $u \ge -1$, and its left derivative
   $\varphi'_g$, at every $u > -1$, are $\varphi'_g(u) = \varphi'_d(u) = 1/(G_0 : G_u)$ if $u$ is not an integer, and
   $\varphi'_g(u) = 1/(G_0 : G_u)$, $\varphi'_d(u) = 1/(G_0 : G_{u+1})$ if $u$ is an integer. At the end point $-1$ there
   is no left derivative, and $\varphi'_d(-1) = 1$, as $\varphi_{L/K}$ is the identity on $[-1, 0]$. These properties
   characterize $\varphi_{L/K}$, and $\varphi_{L/K}$ is a homeomorphism of $[-1, +\infty)$ onto itself.
2. Its inverse $\psi_{L/K}$ is continuous, piecewise linear, increasing and convex, with $\psi_{L/K}(0) = 0$; if
   $v = \varphi_{L/K}(u)$, then $\psi'_d(v) = 1/\varphi'_d(u)$ for every $v \ge -1$ and $\psi'_g(v) = 1/\varphi'_g(u)$ for
   every $v > -1$, so these one-sided derivatives take only integer values; at $-1$ there is no left derivative, and
   $\psi'_d(-1) = 1$. If $v$ is an integer, so is $\psi_{L/K}(v)$.

Serre states the formulas for the left derivatives for every integer $u$; at $u = -1$, where the half-line
$[-1, +\infty)$ ends, there is no left derivative, and the convention for $(G_0 : G_{-1})$ would give the value
$(G_{-1} : G_0)$, which is $2$ for an unramified quadratic extension.
3. For every $u \ge -1$,

    $$\varphi_{L/K}(u) = \frac{1}{g_0} \sum_{s \in G} \min\bigl(i_G(s), u + 1\bigr) - 1.$$

The proof of the integrality in item 2 uses that $g_{m+1}$ divides $g_0, \dots, g_m$, the group $G_{m+1}$ being
a subgroup of each of $G_0, \dots, G_m$.

## Depends on

- [Ramification groups of local fields](../ramification-groups-of-local-fields.md), for the valuation $v_L$ and the groups $G_i$

## Proof depends on

- [Ramification groups of local fields](../ramification-groups-of-local-fields.md), for the groups $G_i$ forming a decreasing sequence of subgroups of $G$ with $G_{-1} = G$ and $G_i = 1$ for large $i$: then $1/(G_0 : G_t)$ is positive, decreasing in $t$ and equal to $1/g_0$ for large $t$, which gives item 1, the count of the $s \in G$ with $i_G(s) \ge m + 2$, which are those of $G_{m+1}$, which gives the derivative of the right side of item 3 on $(m, m + 1)$, and the divisibilities used for item 2

## Sources

- J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer, 1979, Chapter IV:
  - Notation and Hypotheses, p. 61 (a field $K$ complete under a discrete valuation; "We will always assume
    that the residue extension $\overline{L}/\overline{K}$ is separable");
  - §1, Lemma 1 and Proposition 1, pp. 61–62 (the groups $G_i$), and p. 62 (the function
    $i_G(s) = v_L(s(x) - x)$ for an $A_K$-generator $x$ of $A_L$, with $i_G(s) \ge i + 1 \Leftrightarrow s \in G_i$,
    which "shows that the definition of $i_G$ does not depend on the choice of the generator $x$");
  - §3, p. 73: $G_u$ for real $u \ge -1$, the definition of $\varphi$ with the convention for $-1 \le t \le 0$,
    Proposition 12 ("Note that these properties characterise $\varphi$. The map $\varphi$ is a homeomorphism of
    the half-line $[-1, +\infty[$ onto itself. Denote by $\psi$ (or $\psi_{L/K}$) the inverse map."),
    Proposition 13, and the proof of Proposition 13 d), pp. 73–74;
  - §3, Lemma 3, p. 74, with its proof.
