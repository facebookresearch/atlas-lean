# Herbrand's theorem

Let $L/K$ be a finite Galois extension of complete discretely valued fields whose residue fields are perfect
of characteristic $p > 0$, with group $G$ and ramification groups $G_u$ ($u \ge -1$ real) in the lower
numbering, as in [Herbrand's functions](herbrand-functions.md). Let $H$ be a normal subgroup of $G$ and
$K' \subseteq L$ its fixed field, so that $G/H = \operatorname{Gal}(K'/K)$ has its own ramification groups
$(G/H)_v$ and $H = \operatorname{Gal}(L/K')$ has Herbrand's function $\varphi_{L/K'}$. **Herbrand's theorem**
says that for every real $u \ge -1$,

$$G_u H / H = (G/H)_v \qquad \text{with } v = \varphi_{L/K'}(u).$$

Both groups contain the identity, so only their elements $\sigma \neq 1$ need to be compared; for $\sigma = 1$ the
preimage of $\sigma$ in $G$ contains $1$, with $i_G(1) = +\infty$. The proof first shows that for $\sigma \in G/H$,
$\sigma \neq 1$, with $j(\sigma)$ the largest of the integers $i_G(s)$ for $s$ in the preimage of $\sigma$ in $G$, a
finite number as no such $s$ is $1$,

$$i_{G/H}(\sigma) - 1 = \varphi_{L/K'}\bigl(j(\sigma) - 1\bigr).$$

For $s$ a representative with $i_G(s) = j(\sigma) = m$ and $t \in H$, one has $i_G(st) = \min(i_G(t), m)$; the
formula for $i_{G/H}$ of [The function i_G of a quotient](function-i-g-of-a-quotient.md), the equalities
$i_G(t) = i_H(t)$ and $e_{L/K'} = \lvert H_0 \rvert$, and the formula for $\varphi_{L/K'}$ through $i_H$ (item 3 of
[Herbrand's functions](herbrand-functions.md), for the group $H$) give it. Serre states it for every
$\sigma \in G/H$, both sides being infinite at $\sigma = 1$. Then, for $\sigma \neq 1$, $\sigma \in G_u H/H$ if and
only if $j(\sigma) - 1 \ge u$, if and only if $\varphi_{L/K'}(j(\sigma) - 1) \ge \varphi_{L/K'}(u)$, $\varphi_{L/K'}$
being increasing, if and only if $i_{G/H}(\sigma) - 1 \ge v$, that is, $\sigma \in (G/H)_v$.

## Depends on

- [Herbrand's functions](herbrand-functions.md), for the groups $G_u$ and $(G/H)_v$ and the function $\varphi_{L/K'}$

## Proof depends on

- [The function i_G of a quotient](function-i-g-of-a-quotient.md), for $i_{G/H}(\sigma) = \frac{1}{e_{L/K'}} \sum_{s \mapsto \sigma} i_G(s)$
- [Herbrand's functions](herbrand-functions.md), for $\varphi_{L/K'}(u) = \frac{1}{\lvert H_0 \rvert} \sum_{t \in H} \min(i_H(t), u + 1) - 1$, for $\varphi_{L/K'}$ being increasing, and for $s \in G_u \Leftrightarrow i_G(s) \ge u + 1$
- [Ramification groups of local fields](../ramification-groups-of-local-fields.md), for $H_i = G_i \cap H$, which gives $i_H(t) = i_G(t)$ for $t \in H$, and for $H_0$ being the inertia group of $L/K'$, of order $e_{L/K'}$

## Sources

- J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer, 1979, Chapter IV:
  - §1, Proposition 2, p. 62 ("For every $s \in H$, $i_H(s) = i_G(s)$, and $H_i = G_i \cap H$");
  - §3, Lemma 4, pp. 74–75, with its proof, and Lemma 5, p. 75: "If $v = \varphi_{L/K'}(u)$ then
    $G_uH/H = (G/H)_v$. (This statement is usually called "Herbrand's theorem".)", with its proof; Serre
    assumes only that the residue extension is separable.
