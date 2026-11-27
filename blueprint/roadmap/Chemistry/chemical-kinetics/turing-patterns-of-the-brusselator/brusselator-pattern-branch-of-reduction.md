# For b < 1 + a², a Turing pattern branch at an admissible critical mode

Let $a \ne 0$ and $b < 1 + a^2$, so that the [steady state](brusselator-steady-state.md)
$(a, b / a)$ is stable without diffusion, and let $d_u \ge 0$. Let $\iota$ be a finite set of modes
with real wavenumbers $\kappa_i$, write $J$ for the [Brusselator Jacobian](brusselator-jacobian.md)
and $D(d) = \operatorname{diag}(d_u, d)$, and let $L_d$ be the
[mode operator](../../../Analysis/partial-differential-equations/lyapunov-schmidt-reduction-for-turing-pattern-br/mode-operator.md)
$(w_i)_i \mapsto ((J - \kappa_i^2 D(d)) w_i)_i$ on families $w = (w_i)_{i \in \iota}$ of vectors of
$\mathbb{R}^2$ (the Neumann-mode coefficients). Fix a mode $i_0$, write $k = \kappa_{i_0}$, and
assume:

- the mode $i_0$ is admissible, $(b - 1) k^2 - d_u k^4 > 0$, and
  $d_0 = a^2 (1 + d_u k^2) / ((b - 1) k^2 - d_u k^4)$ is its
  [neutral inhibitor diffusion](brusselator-neutral-diffusion.md);
- no other mode is critical at $d_0$: $\det(J - \kappa_i^2 D(d_0)) \ne 0$ for every $i \ne i_0$;
- a Fredholm package of $L_{d_0}$ is fixed (splittings of the domain as $\ker L_{d_0} \oplus X_1$
  and of the codomain as $Y_0 \oplus \operatorname{range} L_{d_0}$, with $L_{d_0}$ an isomorphism
  from $X_1$ onto its range), and the
  [critical mode](../../../Analysis/partial-differential-equations/lyapunov-schmidt-reduction-for-turing-pattern-br/critical-mode.md)
  $\varphi$ lies in $\ker L_{d_0}$;
- $F(w, d)$, a map from pairs of a family $w$ and a real $d$ to families, is strictly
  differentiable at $(0, d_0)$ with a derivative whose partial derivative in $w$ is $L_{d_0}$;
  for every $d$ near $d_0$, $F(0, d) = 0$ and $w \mapsto F(w, d)$ has derivative $L_d$ at
  $w = 0$;
- $G$ is a real function of $(s, d)$, strictly differentiable at $(0, d_0)$, with
  $\tilde G(s, d) = s \, G(s, d)$ near $(0, d_0)$, where $\tilde G$ is the
  [scalar bifurcation function](../../../Analysis/partial-differential-equations/lyapunov-schmidt-reduction-for-turing-pattern-br/ls-scalar.md)
  of $F$ for $\varphi$ and the
  [normalized critical functional](../../../Analysis/partial-differential-equations/bifurcation-of-turing-pattern-branches/normalized-critical-functional.md).

Then:

- $\partial_d G(0, d_0) = \dfrac{d_u k^4 - (b - 1) k^2}{b - 1 - a^2 - k^2 (d_u + d_0)}$, and this
  number is positive;
- for $d$ near $d_0$, $G(0, d)$ has the sign of the
  [leading eigenvalue](../../../Analysis/partial-differential-equations/bifurcation-of-turing-pattern-branches/leading-eigenvalue.md)
  $\frac{1}{2} (\operatorname{tr} M + \sqrt{\operatorname{tr}^2 M - 4 \det M})$ of
  $M = J - k^2 D(d)$;
- there is a function $\beta$ with $\beta(0) = d_0$, strictly differentiable at $0$ with
  $\beta'(0) = -\partial_s G(0, d_0) / \partial_d G(0, d_0)$, such that near $(0, d_0)$ the zeros
  of $F$ are exactly the pairs $(0, d)$ and the pairs $(s \varphi + W(s \varphi, d), d)$ with
  $d = \beta(s)$, where $W$ is the
  [Lyapunov–Schmidt solution operator](../../../Analysis/partial-differential-equations/lyapunov-schmidt-reduction-for-turing-pattern-br/ls-solution.md);
- for every small $s \ne 0$, the family $s \varphi + W(s \varphi, \beta(s))$ is nonzero and is a
  zero of $F$ at $d = \beta(s)$: a pattern;
- near $d_0$, $G(0, d) < 0$ for $d < d_0$ and $G(0, d) > 0$ for $d > d_0$.

The map $F$ is a hypothesis: no Galerkin projection of the Brusselator nonlinearity is constructed,
and the factorization of the scalar bifurcation function is assumed. Only the selected mode is
controlled, and nothing is claimed about the stability of the branch.
