# Belyi covers of the modular curve $X(2)$ and their cusp charts

This node is still to be broken down. Let $\mathbb{H}$ be the complex upper half-plane, with
$\mathrm{SL}_2(\mathbb{R})$ acting by Möbius transformations, and let

$$\Gamma(2) = \left\{ \begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \mathrm{SL}_2(\mathbb{Z}) :
a \equiv d \equiv 1 \bmod 2, \ b \equiv c \equiv 0 \bmod 2 \right\}.$$

Let $Y(2) = \Gamma(2) \backslash \mathbb{H}$ and let $X(2)$ be the compact Riemann surface obtained
by adding the cusps $0$, $1$ and $\infty$; the modular lambda function induces an isomorphism
$\lambda \colon X(2) \to \mathbb{P}^1(\mathbb{C})$. For each cusp $\kappa$ fix $\gamma_\kappa \in
\mathrm{SL}_2(\mathbb{Z})$ with $\gamma_\kappa(\kappa) = \infty$. Let $\dot B_\kappa$ be the image
in $Y(2)$ of the strip $\dot S_\infty = \{x + iy : -1 \le x < 1, \ y > \tfrac12\}$ under $\tau
\mapsto \Gamma(2) \gamma_\kappa \tau$, and $B_\kappa = \dot B_\kappa \cup \{\kappa\}$. The function
$z_\kappa(\tau) = \exp(\pi i \gamma_\kappa^{-1} \tau + \pi/2)$ induces a chart $z_\kappa \colon
B_\kappa \to B(0, 1)$ onto the open unit disc, and $\{(B_\kappa, z_\kappa)\}_\kappa$ is an atlas
of $X(2)$.

A **Belyi cover** of $X(2)$ is a morphism of compact connected Riemann surfaces $\pi \colon Y \to
X(2)$ that is unramified over $Y(2)$; the points of $Y$ not lying over $Y(2)$ are its **cusps**.
For a cusp $y$ over $\kappa$, let $\dot V_y$ be the connected component of $\pi^{-1} \dot
B_\kappa$ whose closure $V_y$ in $\pi^{-1}(B_\kappa)$ contains $y$. There are a positive integer
$e_y$, the ramification index of $y$ over $\kappa$, and an isomorphism $w_y \colon V_y \to B(0, 1)$
with $w_y^{e_y} = z_\kappa \circ \pi|_{V_y}$; the **cusp charts** $\{(V_y, w_y)\}_y$ form an atlas
of $Y$. Put $s_1 = \sqrt{1/2}$, define $r_1$ by $r_1^{\deg \pi} = s_1$ (so $\frac12 < r_1 < 1$),
and let $V_y^{r_1} = \{x \in V_y : \lvert w_y(x) \rvert < r_1\}$.

A finite morphism $Y \to \mathbb{P}^1_{\mathbb{C}}$ of compact connected Riemann surfaces that is
unramified over $\mathbb{P}^1 \setminus \{0, 1, \infty\}$, composed with $\lambda^{-1}$, is a
Belyi cover of $X(2)$ of the same degree.

## Depends on

None among the pages; $\mathbb{H}$, $\Gamma(2)$ and the modular lambda function are classical.

## Proof depends on

Its proof uses the inputs listed under Expansion.

## Expansion

A good expansion has pages for: the compact Riemann surface $X(2)$ and the isomorphism $\lambda$
(§4.4, p. 119); the injectivity of the strip $\dot S_\infty$ into $Y(2)$ and the charts
$z_\kappa$ (§3.2, pp. 105–106); the classification of connected finite covers of the punctured
disc, which gives the cusp charts $w_y$ (p. 106); and Lemma 3.2.2, $g \le \deg \pi$ for a Belyi
cover with $Y$ of genus $g$, from the Riemann–Hurwitz formula (p. 106).

## Sources

- A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8 (2014), 89–140, <https://doi.org/10.2140/ant.2014.8.89>, §3.2, pp. 105–106 (atlas of $X(2)$, Definition 3.2.1, cusp charts, Lemma
  3.2.2), Definition 3.4.4, p. 110, and proof of Theorem 4.5.1, p. 122 (composition with
  $\lambda^{-1}$). The printed chart formula $\exp(\pi i \gamma_k^{-1} \tau + \pi/2)$ on p. 106
  writes $k$ for $\kappa$.
