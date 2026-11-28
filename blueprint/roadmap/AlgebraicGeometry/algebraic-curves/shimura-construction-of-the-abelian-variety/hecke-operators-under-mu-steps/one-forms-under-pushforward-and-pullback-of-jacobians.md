# Holomorphic $1$-forms under the pushforward and the pullback of Jacobians

Let $\pi \colon X' \to X$ be a nonconstant holomorphic map of compact Riemann surfaces, with
[Jacobians](../../jacobians-of-compact-riemann-surfaces/jacobian.md) $J(X')$ and $J(X)$, and let
$\pi_* \colon J(X') \to J(X)$ and $\pi^* \colon J(X) \to J(X')$ be the
[pushforward](../../jacobians-of-compact-riemann-surfaces/pushforward.md) and the
[pullback](../../jacobians-of-compact-riemann-surfaces/pullback.md) on Jacobians. Identify the
holomorphic $1$-forms $D_{J(X)}$ on $J(X)$ with the holomorphic differentials $\Omega^1(X)$ on $X$, and $D_{J(X')}$ with
$\Omega^1(X')$, by pullback along Abel–Jacobi maps, as in
[pullback of holomorphic $1$-forms along an Abel–Jacobi map](../cusp-forms-as-one-forms-steps/pullback-of-one-forms-along-the-abel-jacobi-map.md).
Then:

1. the pullback of $1$-forms along $\pi_*$, $D_{J(X)} \to D_{J(X')}$, is the pullback of differentials
   $\pi^* \colon \Omega^1(X) \to \Omega^1(X')$;
2. the pullback of $1$-forms along $\pi^*$, $D_{J(X')} \to D_{J(X)}$, is the trace
   $\mathrm{Tr}_\pi \colon \Omega^1(X') \to \Omega^1(X)$, which on an open set $U \subset X$ over which $\pi$ is unramified
   and has holomorphic sections $s_1, \dots, s_d$ with disjoint images covering $\pi^{-1}(U)$ sends $\eta$ to
   $\sum_j s_j^* \eta$, and which extends holomorphically over the branch points.

## Depends on

- [Jacobian of a compact Riemann surface](../../jacobians-of-compact-riemann-surfaces/jacobian.md)
- [Pushforward on Jacobians](../../jacobians-of-compact-riemann-surfaces/pushforward.md)
- [Pullback on Jacobians](../../jacobians-of-compact-riemann-surfaces/pullback.md)
- [The pushforward on Jacobians is holomorphic](../../jacobians-of-compact-riemann-surfaces/pushforward-cont-mdiff.md),
  for the pullback of holomorphic $1$-forms along $\pi_*$
- [The pullback map on Jacobians is holomorphic](../../jacobians-of-compact-riemann-surfaces/pullback-cont-mdiff.md),
  for the pullback of holomorphic $1$-forms along $\pi^*$
- [Pullback of holomorphic $1$-forms along an Abel–Jacobi map](../cusp-forms-as-one-forms-steps/pullback-of-one-forms-along-the-abel-jacobi-map.md),
  for the identifications of $D_{J(X)}$ and $D_{J(X')}$ with the holomorphic differentials

## Proof depends on

- [Pullback of holomorphic $1$-forms along an Abel–Jacobi map](../cusp-forms-as-one-forms-steps/pullback-of-one-forms-along-the-abel-jacobi-map.md),
  for the identifications, their independence of the base points, and the classical model of the Jacobian in which
  they are computed
- [Abel–Jacobi map](../../jacobians-of-compact-riemann-surfaces/of-curve.md), for the Abel–Jacobi
  maps of $X$ and $X'$

## Proof sketch

Item 1, in the classical models $J(X) = \Omega^1(X)^\vee / H_1(X, \mathbb{Z})$ and
$J(X') = \Omega^1(X')^\vee / H_1(X', \mathbb{Z})$, where the Abel–Jacobi map $\varphi_P$ of $X$ based at $P$ sends $Q$ to the
class of $\omega \mapsto \int_P^Q \omega$, and $\varphi'_{P'}$ is the Abel–Jacobi map of $X'$ based at $P'$. There $\pi_*$ is
induced by the linear map $\Omega^1(X')^\vee \to \Omega^1(X)^\vee$, $\lambda \mapsto \lambda \circ \pi^*$, the transpose of the
pullback of differentials $\pi^* \colon \Omega^1(X) \to \Omega^1(X')$; this map sends $H_1(X', \mathbb{Z})$ into
$H_1(X, \mathbb{Z})$, as $\int_\gamma \pi^*\omega = \int_{\pi \circ \gamma} \omega$ for every closed path $\gamma$ in $X'$. For
$P', Q' \in X'$ and a path $c'$ from $P'$ to $Q'$, the path $\pi \circ c'$ runs from $\pi(P')$ to $\pi(Q')$, and

$$\int_{c'} \pi^*\omega = \int_{\pi \circ c'} \omega \qquad (\omega \in \Omega^1(X)),$$

that is, $\int_{P'}^{Q'} \pi^*\omega = \int_{\pi(P')}^{\pi(Q')} \omega$. So $\pi_* \circ \varphi'_{P'} = \varphi_{\pi(P')} \circ \pi$.
Pulling back $1$-forms along both sides gives $(\varphi'_{P'})^* \circ (\pi_*)^* = \pi^* \circ (\varphi_{\pi(P')})^*$ on
$D_{J(X)}$, where $(\pi_*)^*$ is the pullback of $1$-forms along $\pi_*$; as the identifications do not depend on the base
points, this is item 1. Equivalently, the differential of $\pi_*$ at the origin is $\lambda \mapsto \lambda \circ \pi^*$, so
$\pi_*$ pulls the invariant $1$-form on $J(X)$ with value $\lambda \mapsto \lambda(\omega)$ at the origin back to the
invariant $1$-form on $J(X')$ with value $\mu \mapsto \mu(\pi^*\omega)$.

Item 2, in the classical model $J(X') = \Omega^1(X')^\vee / H_1(X', \mathbb{Z})$, where the invariant $1$-form $\omega_\eta$
that corresponds to $\eta \in \Omega^1(X')$ has the value $\mu \mapsto \mu(\eta)$ at every point. Fix $P \in X$ and let $\varphi_P$
be the Abel–Jacobi map of $X$ based at $P$. For $Q \in X$, the pullback of the divisor $Q - P$ is the sum of the points
over $Q$ minus the sum of the points over $P$, counted with their ramification indices. If $Q$ and $P$ are not branch
points and $c$ is a path from $P$ to $Q$ that avoids the branch points, with lifts $c_1, \dots, c_d$ to $X'$, then

$$\sum_{j=1}^{d} \int_{c_j} \eta' = \int_c \mathrm{Tr}_\pi \eta' \qquad (\eta' \in \Omega^1(X')),$$

as over a disc on which $\pi$ is unramified the lifts are the images of $c$ under the sections $s_j$. So
$\pi^* \circ \varphi_P$ sends $Q$ to the class of $\eta' \mapsto \int_P^Q \mathrm{Tr}_\pi \eta'$, and the pullback of $\omega_\eta$ along
it is $\mathrm{Tr}_\pi \eta$, first away from the branch points and then everywhere. As $\pi^*$ is a holomorphic homomorphism,
the pullback of $\omega_\eta$ along $\pi^*$ is a translation-invariant $1$-form on $J(X)$, determined by its pullback
along $\varphi_P$, which is $\mathrm{Tr}_\pi \eta$; this is item 2. Equivalently, the differential of $\pi^*$ at the origin is
the transpose $\lambda \mapsto \lambda \circ \mathrm{Tr}_\pi$ of the trace.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the description of $\pi_*$ in the classical models as the map induced by the transpose $\lambda \mapsto \lambda \circ \pi^*$
  of the pullback of differentials, and the compatibility $\pi_* \circ \varphi'_{P'} = \varphi_{\pi(P')} \circ \pi$ of the
  pushforward with the Abel–Jacobi maps, which follows from $\int_{P'}^{Q'} \pi^*\omega = \int_{\pi(P')}^{\pi(Q')} \omega$
  and gives item 1 by pulling back $1$-forms;
- the description of $\pi^*$ in the classical model $\Omega^1(X)^\vee / H_1(X, \mathbb{Z})$ as the map induced by the
  transpose of $\mathrm{Tr}_\pi$, from $\int_{\pi^{-1}(c)} \eta = \int_c \mathrm{Tr}_\pi \eta$ for a path $c$ in $X$ avoiding the
  branch points, from which item 2 follows on the translation-invariant $1$-forms;
- the holomorphy of $\mathrm{Tr}_\pi \eta$ at the branch points of $\pi$.

## Sources

- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: §1, p. 525 (the homomorphism $\{\Gamma' \alpha \Gamma\}$
  attached to the correspondence $X(\Gamma' \alpha \Gamma)$ "as in Weil [15, §VI]", and (1.3), introduced with "Now the
  commutative diagrams (7.2.2) and (7.2.6) of [11] imply").
- J. S. Milne, *Modular Functions and Modular Forms*, course notes, version 1.31 (2017),
  <https://www.jmilne.org/math/CourseNotes/MF.pdf>: p. 115 (for a curve $C$ over $\mathbb{C}$, $H_1(C, \mathbb{Z})$ as a
  lattice in $\Omega^1(C)^\vee$ through $\gamma \mapsto (\omega \mapsto \int_\gamma \omega)$, the Jacobian variety $J$ with
  $J(\mathbb{C}) = \Omega^1(C)^\vee / H_1(C, \mathbb{Z})$, and, from Abel's theorem and the Jacobi inversion formula, the
  isomorphism $\sum n_i P_i \mapsto (\omega \mapsto \sum n_i \int_{\gamma_i} \omega)$ of the divisors of degree zero modulo
  the principal divisors onto $J(\mathbb{C})$, for paths $\gamma_i$ from a fixed point $P$ to $P_i$).
- K. A. Ribet and W. A. Stein, *Lectures on Modular Forms and Hecke Operators*, version of January 12, 2017,
  <https://wstein.org/books/ribet-stein/main.pdf>: §12.3, p. 100 (the Albanese construction
  $\mathrm{Jac}(X) = H^0(X, \Omega^1)^* / \iota(H_1(X, \mathbb{Z}))$, with $\iota(\gamma) = \int_\gamma$, in which a morphism
  $X \to Y$ of curves induces $\mathrm{Jac}(X) \to \mathrm{Jac}(Y)$ through the resulting map
  $H^0(X, \Omega^1)^* \to H^0(Y, \Omega^1)^*$ on tangent spaces, while for the Jacobian viewed as $\mathrm{Pic}^0$ the
  pullback of divisor classes gives $\mathrm{Jac}(Y) \to \mathrm{Jac}(X)$); §13.5.3, p. 124 (for $P \in X$, the embedding of
  $X$ into its Jacobian given by the functionals $\omega \mapsto \int_P^Q \omega$).
- G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Publ. Math. Soc. Japan 11, Iwanami
  Shoten and Princeton University Press, 1971: (7.2.2) and (7.2.6), as cited in Shimura (1973) above, p. 525; not read
  for this page.
- A. Weil, *Variétés abéliennes et courbes algébriques*, Hermann, Paris, 1948: §VI, as cited in Shimura (1973) above,
  p. 525; not read for this page.
