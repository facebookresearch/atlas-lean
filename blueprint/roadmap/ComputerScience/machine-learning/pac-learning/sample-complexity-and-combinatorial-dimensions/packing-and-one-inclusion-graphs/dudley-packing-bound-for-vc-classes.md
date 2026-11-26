# Dudley's packing bound for classes of bounded VC dimension

Let $C$ be a class of functions $X \to \{0,1\}$ such that every finite set shattered by $C$ has at most $d$ points, let $x = (x_1, \dots, x_m) \in X^m$ with $m \ge 1$, and let $0 < \varepsilon \le 1$. Call a set $P$ of labelings in $C|_x = \{(c(x_1), \dots, c(x_m)) : c \in C\}$ $\varepsilon$-separated if any two distinct members of $P$ differ in at least $\varepsilon m$ coordinates. Then

$$
|P| \le \left(\frac{8}{\varepsilon}\right)^{2d},
$$

a bound independent of $m$. More precisely (subsampling step), if $2 \ln |P| < \varepsilon k$ for an integer $k$, then some $k$ positions, possibly repeated, already distinguish all members of $P$, so $|P| \le \Pi_C(k)$, where $\Pi_C$ is the growth function. Consequently every finite set of realized labelings contains an $\varepsilon$-separated subset whose Hamming balls of radius $\varepsilon m$ cover it, and this covering net has at most $(8/\varepsilon)^{2d}$ points.

## Proof sketch

A uniformly random $k$-tuple of positions fails to separate a fixed pair of $\varepsilon$-separated labelings with probability at most $(1-\varepsilon)^k \le e^{-\varepsilon k}$, so when $|P|^2 e^{-\varepsilon k} < 1$ a union bound over pairs yields a tuple separating all pairs; the restricted labelings are then distinct, giving $|P| \le \Pi_C(k)$. Choosing $k = \lfloor 2\ln|P|/\varepsilon \rfloor + 1$ and the Sauer bound $\Pi_C(k) \le e^{k/T} T^d$ with $T = 4/\varepsilon$ and solving for $|P|$ gives $(8/\varepsilon)^{2d}$.

## Depends on

- [Growth function](../../../../not-yet-classified/growth-function/growth-function.md)
- [The VC dimension is at most the size of the ground set](../../../../../Combinatorics/extremal-set-theory/vc-dim-le-card.md)

## Proof depends on

- [Sauer bound for the growth function](../../../../not-yet-classified/growth-function/growth-function-le-sum.md)

## Sources

- R. M. Dudley, "Central Limit Theorems for Empirical Measures", The Annals of Probability, 1978.
- R. Vershynin, "High-Dimensional Probability: An Introduction with Applications in Data Science", Cambridge University Press, 2018.
