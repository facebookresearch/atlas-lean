# Beurling–Deny: the unit contraction operates on a closed form iff its resolvent is Markovian

Let $m$ be a $\sigma$-finite measure on $X$ and $\mathcal E$ a [closed](is-closed.md) [symmetric
form](symmetric-form.md) on $L^2(X; m)$. For $\alpha > 0$ and $f \in L^2(X; m)$, the resolvent
$G_\alpha f$ is the element $u \in D[\mathcal E]$ with
$\mathcal E(u, v) + \alpha (u, v) = (f, v)$ for all $v \in D[\mathcal E]$ (equation (1.3.7) of
Fukushima, Oshima and Takeda). Then [the unit contraction operates on
$\mathcal E$](unit-contraction-operates.md) if and only if every $\alpha G_\alpha$ is Markovian: for
all $\alpha > 0$, $f \in L^2(X; m)$ and $u \in D[\mathcal E]$ with
$\mathcal E(u, v) + \alpha (u, v) = (f, v)$ for every $v \in D[\mathcal E]$, if $0 \le f \le 1$
$m$-a.e. then $0 \le \alpha u \le 1$ $m$-a.e.

This is Theorem 1.4.1, (b) ⇔ (d), of Fukushima, Oshima and Takeda; condition (E.4)′ is equivalent
for closed forms to their Markov condition (E.4). They prove (b) ⇒ (e) under their topological
assumption (1.1.7) and note (footnote 10) that it holds without it, referring to Ma and Röckner
(1992) and Bouleau and Hirsch (1991); the statement above has no topological assumption.

## Sources

- M. Fukushima, Y. Oshima and M. Takeda, *Dirichlet Forms and Symmetric Markov Processes*, 2nd revised and extended ed., de Gruyter Studies in Mathematics 19, de Gruyter, 2011, Theorem 1.4.1 and equation (1.3.7).
