# Mass-action rates are locally Lipschitz

Let $G$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
finite species set $S$ and reaction set $\rho$, let $\kappa \in \mathbb{R}^\rho$ be any real rate
constants (nonnegative in the model) and $r$ a reaction. The
[mass-action rate](../../../Biology/systems-biology/complex-balancing-and-the-deficiency-zero-theore/rate.md)
of $r$,

$$u \mapsto \kappa_r \prod_{s \in S} u_s^{\mathrm{src}(r)_s},$$

is locally Lipschitz on $\mathbb{R}^S$: every point has a neighbourhood on which it is Lipschitz. It
is a polynomial, hence continuously differentiable.
