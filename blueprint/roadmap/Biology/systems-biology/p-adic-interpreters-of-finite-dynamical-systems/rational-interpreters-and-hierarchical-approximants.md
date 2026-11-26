# Rational interpreters and hierarchical approximants of finite dynamical systems

**Setting.** Let $f : \mathcal{C} \to \mathcal{C}$ be a finite dynamical system on $\mathcal{C} = \mathbb{F}_p^N$, for example a multistate model of a gene regulatory network. Fix an ordering of the $N$ coordinates and encode $a = (a_1,\dots,a_N)$ as $m_a = \sum_{j} a_j p^{j-1}$. The *coarse embedding* $\iota$ sends $a$ to the closed ball $\bar B_{1/p^N}(m_a) \subset \mathbb{Z}_p$, a bijection of $\mathcal{C}$ onto $\mathbb{Z}_p/p^N\mathbb{Z}_p$; two configurations share a ball of radius $p^{-n}$ iff their first $n$ ordered coordinates agree. A rational function $\phi \in \mathbb{C}_p(z)$ *interprets* $f$ if it maps the ball of each $a$ into the ball of $f(a)$, and is *exact* if $\phi(\bar B(a)) = \bar B(f(a))$.

**Theorem (existence of interpreters).** For every $f$ and every embedding $\iota$ there is a rational $\phi \in \mathbb{C}_p(z)$ interpreting $f$, and an exact interpreter exists.

**Canonical targets.** For a level-$n$ ball $\bar B_{1/p^n}(m)$, $m \in \{0,\dots,p^n-1\}$, let $\bar B_{t_{n,m}}(\beta_{n,m})$ with $t_{n,m} = p^{-M_{n,m}}$ be the smallest ball of the hierarchy containing all $m_{f(a)}$ with $a$ truncating to $m$.

**Theorem (hierarchical approximants).** For every resolution $n \in \{0,\dots,N\}$ there is $F_n \in \mathbb{C}_p(z)$ with

$$F_n\bigl(\bar B_{1/p^n}(m)\bigr) = \bar B_{t_{n,m}}(\beta_{n,m}) \quad \text{for every } m,$$

and for an exact interpreter $\phi$, $|\phi(z) - F_n(z)|_p \le p^{-M_{n,m}}$ on $\bar B_{1/p^n}(m) \cap \mathbb{Z}_p$.

The ratios $t_{n,m}/p^{-n}$ act as discrete multipliers: they measure whether $f$ contracts or expands the coordinate hierarchy at resolution $n$ around $m$.

## Expansion

Non-Archimedean rational maps send balls to balls (or onto the projective line), with constant preimage counts, so prescribing images of finitely many disjoint rational balls is a finite interpolation problem; a gluing theorem for rational maps on disjoint balls solves it with arbitrary precision. Exactness follows by choosing each local piece to map its ball onto the target ball. A ball mapped strictly inside itself has a unique attracting fixed point, which links the ball-image radii to attractors of the finite system. Expanding cases need a pole placed on a sphere of half-integer exponent, a device with no real-analytic counterpart. Results depend on the coordinate ordering, which is a modelling choice.

## Sources

- J. R. Pérez-Buendía, V. Nopal-Coello, "Hierarchical Expansion of Finite Discrete Dynamical Systems: A Non-Archimedean Variational Theory over Coordinate Orderings" (2026), Section 2 (coarse embedding), Theorem 3.3, Proposition 3.5, Definition of the $n$-th approximation, Theorem 3.11 and Proposition 3.13, <https://doi.org/10.48550/arXiv.2603.14097>.
