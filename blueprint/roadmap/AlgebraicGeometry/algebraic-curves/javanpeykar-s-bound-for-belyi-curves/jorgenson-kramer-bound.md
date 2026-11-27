# Bound for the Arakelov form of a Belyi cover in the hyperbolic metric

This node is still to be broken down. Let $\pi \colon Y \to X(2)$ be a
[Belyi cover](belyi-cover-of-x2.md) with $Y$ of positive genus $g$. The topological fundamental
group of $Y(2)$ is $\Gamma(2)/\{\pm 1\}$, so $\pi^{-1}(Y(2)) = \Gamma' \backslash \mathbb{H}$ for a
subgroup $\Gamma' \subset \Gamma(2)/\{\pm 1\}$ of finite index; let $\Gamma \subset \Gamma(2)$ be
its inverse image, a cofinite Fuchsian group without elliptic elements. Let $\mu_{\mathrm{hyp}} =
\frac{i}{2} \frac{1}{\Im(\tau)^2} \, d\tau \, d\overline{\tau}$ be the hyperbolic metric and $\mu$
the [Arakelov $(1,1)$-form](../arakelov-invariants-of-curves/arakelov-green-function.md) of $Y$, and let $F_\Gamma \colon
Y \to [0, \infty)$ be the unique smooth function vanishing at the cusps such that $\mu =
\frac{1}{g} F_\Gamma \, \mu_{\mathrm{hyp}}$. Then

$$\sup_{\tau \in Y} F_\Gamma \le 64 \max_{y \in Y} (e_y)^2 \le 64 (\deg \pi)^2,$$

where $e_y$ is the ramification index of $y$ over $X(2)$.

## Depends on

- [Belyi covers of the modular curve $X(2)$](belyi-cover-of-x2.md)
- [Arakelov $(1,1)$-form and Arakelov–Green function](../arakelov-invariants-of-curves/arakelov-green-function.md)

## Proof depends on

Its proof uses the inputs listed under Expansion.

## Expansion

Javanpeykar takes the bound from Bruin's explicit version of a result of Jorgenson and Kramer,
published in Mathematika (see Sources), which was not read here. In the numbering of the 2013
preprint that Javanpeykar cites: Bruin shows $N_{\mathrm{SL}_2(\mathbb{Z})}(z, 2a^2 - 1) \le 58$
for $a = 1.44$, hence $\sup_z N_\Gamma(z, z, 2a^2 - 1) \le 58$ (Section 8.2), and applies
Proposition 6.1 and Lemma 6.2 with $\epsilon = 2 \deg \pi$. A good expansion reads the published
version, checks these locators against its numbering, and has pages for the existence and
uniqueness of $F_\Gamma$, the hyperbolic lattice-point counts $N_\Gamma$, and those two results.

## Sources

- A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8 (2014), 89–140, <https://doi.org/10.2140/ant.2014.8.89>, §3.3, eq. (7), Definition 3.3.1 and Theorem 3.3.2, p. 107.
- P. Bruin, *Explicit bounds on automorphic and canonical Green functions of Fuchsian groups*,
  Mathematika 60 (2014), 257–306, <https://doi.org/10.1112/S0025579314000060> (not read here).
  Javanpeykar cites it as a 2013 preprint, to appear in Mathematika, with the locators Section 8.2,
  Proposition 6.1 and Lemma 6.2 (p. 107); those locators are the preprint's, as cited by
  Javanpeykar, and have not been checked against the published numbering.
- J. Jorgenson and J. Kramer, *Bounding the sup-norm of automorphic forms*, Geom. Funct. Anal. 14
  (2004), 1267–1277, as cited by Javanpeykar, Remark 3.3.3, p. 107, for a stronger nonexplicit
  version (not read here).
