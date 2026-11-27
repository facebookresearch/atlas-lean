# Hecke operators on cusp forms and Hecke endomorphisms of the Jacobian

Let $N$ be a positive integer, $\Gamma$ a group of level $N$, $J$ the Jacobian of the
[modular curve $X_\Gamma$](../../../../NumberTheory/modular-forms-q-series/modular-forms/modular-curve-of-a-group-of-level-n.md), with $J(\mathbb{C})$ the Jacobian of
$\mathfrak{H}^*/\Gamma$, and let $\mu \colon S_2(\Gamma) \to D_J$ be the isomorphism of
[weight-two cusp forms with holomorphic $1$-forms](../cusp-forms-as-one-forms-steps/cusp-forms-as-one-forms-on-the-modular-jacobian.md). For
$\alpha \in \mathrm{GL}_2(\mathbb{Q})$ with $\det \alpha > 0$, let $[\Gamma \alpha \Gamma]_2$ be the operator on $S_2(\Gamma)$ of
[Hecke operators of level $N$](../../../../NumberTheory/modular-forms-q-series/modular-forms/hecke-operators-of-level-n.md), and $\{\Gamma \alpha \Gamma\}$ the endomorphism of
$J$ of [Hecke endomorphisms](../../../../NumberTheory/modular-forms-q-series/modular-forms/hecke-endomorphisms-of-the-modular-jacobian.md). Then

$$\mu \circ [\Gamma \alpha \Gamma]_2 = \delta\{\Gamma \alpha \Gamma\} \circ \mu,$$

with $\delta$ the pullback of [holomorphic $1$-forms](../holomorphic-one-forms-steps/holomorphic-one-forms-and-tangent-space.md). Consequently, for
every $n \ge 1$, the Hecke operator $T_n$ and the Hecke endomorphism $\xi_n$ satisfy

$$\mu \circ T_n = \delta\xi_n \circ \mu, \qquad \text{that is}, \qquad \mu(g \mid T_n) = \delta\xi_n(\mu(g)) \quad (g \in S_2(\Gamma)).$$

In particular, if $f \in S_2(\Gamma)$ satisfies $f \mid T_n = a_n f$ for all $n$, then $\delta\xi_n$ maps $\mu(f)$ onto
$a_n \mu(f)$.

The first identity is the case $\Gamma' = \Gamma$ of Shimura's (1.3), which he states for a second group $\Gamma'$ of
level $M$, with its own Jacobian $J'$ and isomorphism $\mu'$, and for $\alpha \in \mathbb{R} \cdot \mathrm{GL}_2(\mathbb{Q})$ with
$\det(\alpha) > 0$, in the form $\mu \circ [\Gamma' \alpha \Gamma]_2 = \delta\{\Gamma' \alpha \Gamma\} \circ \mu'$.

## Depends on

- [Weight-two cusp forms as holomorphic $1$-forms on the modular Jacobian](../cusp-forms-as-one-forms-steps/cusp-forms-as-one-forms-on-the-modular-jacobian.md)
- [Modular curve of a group of level $N$ and its standard model over $\mathbb{Q}$](../../../../NumberTheory/modular-forms-q-series/modular-forms/modular-curve-of-a-group-of-level-n.md), for $J$
- [Hecke operators $T_n$ on weight-two cusp forms for a group of level $N$](../../../../NumberTheory/modular-forms-q-series/modular-forms/hecke-operators-of-level-n.md)
- [Hecke endomorphisms $\xi_n$ of the Jacobian of a modular curve](../../../../NumberTheory/modular-forms-q-series/modular-forms/hecke-endomorphisms-of-the-modular-jacobian.md)
- [Holomorphic $1$-forms and tangent space of a complex abelian variety](../holomorphic-one-forms-steps/holomorphic-one-forms-and-tangent-space.md), for $\delta$

## Proof depends on

- [Double coset operators on weight-two cusp forms as maps of differentials](double-coset-operators-on-differentials.md),
  for $\omega_{f \mid [\Gamma \alpha \Gamma]_2} = \mathrm{Tr}_{\pi_1}(\pi_2^* \omega_f)$
- [Holomorphic $1$-forms under the pushforward and the pullback of Jacobians](one-forms-under-pushforward-and-pullback-of-jacobians.md),
  for the pullback of $1$-forms along $(\pi_2)_*$ and $\pi_1^*$
- [Weight-two cusp forms as holomorphic differentials on $\mathfrak{H}^*/\Gamma$](../cusp-forms-as-one-forms-steps/weight-two-cusp-forms-as-holomorphic-differentials.md),
  for $\omega_f$, which corresponds to $\mu(f)$ under pullback along an Abel–Jacobi map
- [Weight-two cusp forms as holomorphic $1$-forms on the modular Jacobian](../cusp-forms-as-one-forms-steps/cusp-forms-as-one-forms-on-the-modular-jacobian.md), for $\mu$
- [Holomorphic $1$-forms and tangent space of a complex abelian variety](../holomorphic-one-forms-steps/holomorphic-one-forms-and-tangent-space.md), for the behaviour of $\delta$ under sums and composition
- [Hecke operators $T_n$ on weight-two cusp forms for a group of level $N$](../../../../NumberTheory/modular-forms-q-series/modular-forms/hecke-operators-of-level-n.md), for $T_n = T_m T_q$
- [Hecke endomorphisms $\xi_n$ of the Jacobian of a modular curve](../../../../NumberTheory/modular-forms-q-series/modular-forms/hecke-endomorphisms-of-the-modular-jacobian.md),
  for $\{\Gamma \alpha \Gamma\} = (\pi_2)_* \circ \pi_1^*$ and $\xi_n = \xi_m \xi_q$

## Proof sketch

Identify $D_J$ with the holomorphic differentials on $\mathfrak{H}^*/\Gamma$ by pullback along an Abel–Jacobi map, so
that $\mu(f)$ corresponds to $\omega_f$. As $\delta$ reverses composition,
$\delta\{\Gamma \alpha \Gamma\} = \delta(\pi_1^*) \circ \delta((\pi_2)_*)$, which corresponds to $\mathrm{Tr}_{\pi_1} \circ \pi_2^*$, and
this sends $\omega_f$ to $\omega_{f \mid [\Gamma \alpha \Gamma]_2}$; so $\delta\{\Gamma \alpha \Gamma\}(\mu(f)) =
\mu(f \mid [\Gamma \alpha \Gamma]_2)$. Summing over the double cosets $\Gamma \beta \Gamma$ gives $\mu \circ T_q = \delta\xi_q \circ \mu$,
as $\delta$ is additive, and $\mu \circ T_m = \delta\xi_m \circ \mu$ is the case $\alpha = \begin{pmatrix} 1 & 0 \\ 0 & m \end{pmatrix}$. For
$n = mq$, with the right action $g \mid T_n = (g \mid T_m) \mid T_q$,

$$\mu(g \mid T_n) = \delta\xi_q\bigl(\delta\xi_m(\mu(g))\bigr) = \delta(\xi_m \xi_q)(\mu(g)) = \delta\xi_n(\mu(g)),$$

since $\delta(\xi_m \circ \xi_q) = \delta\xi_q \circ \delta\xi_m$. For an eigenfunction, $\delta\xi_n(\mu(f)) = \mu(f \mid T_n) = a_n \mu(f)$.

## Sources

- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: §1, p. 525 ((1.3), "the commutative diagrams (7.2.2) and (7.2.6) of [11] imply", the definitions of
  $T_n$ and $\xi_n$, and $\mu \circ T_n = \delta\xi_n \circ \mu$); p. 526 ("By (1.3), we see that $\delta\xi_n$ maps $\mu(f)$
  onto $a_n \cdot \mu(f)$", in the proof of Theorem 1).
- G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Publ. Math. Soc.
  Japan 11, Iwanami Shoten and Princeton University Press, 1971: (7.2.2), (7.2.6) and §3.4, as cited in Shimura (1973) above; not read for this page.
