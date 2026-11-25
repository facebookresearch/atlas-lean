# Global convergence of the chemostat

This node covers the following theorem for the single-species chemostat with Monod growth, in the setting and notation of
the equilibrium page ($D, y, \mu_m, K_s > 0$ and $S_f > 0$): when $D < D_c$, every solution with $X(0) > 0$ and
$S(0) \ge 0$ converges to the interior steady state $(X^*, S^*)$. The restriction to the closed quadrant is part of the
claim. Its proof needs an argument about two-dimensional global dynamics beyond the local results and the invariant region
in this folder.

## Depends on

- [Chemostat equilibria and the washout threshold](chemostat-equilibria-and-washout.md), for $D_c$ and the interior steady state

## Proof depends on

- [Forward invariance and global existence for the chemostat](chemostat-invariance-and-global-existence.md), for the invariant quadrant and existence on $[0, \infty)$

## Expansion

A good expansion states the global convergence theorem with its hypotheses ($S_f > 0$, $D < D_c$, $X(0) > 0$ and
$S(0) \ge 0$), from a checked locator, and links the local stability result for the interior steady state that it uses.

## Sources

- H. L. Smith and P. Waltman, *The Theory of the Chemostat: Dynamics of Microbial Competition*, Cambridge University Press, 1995, Chapter 1.
