# Negative answer to the cocompact asymptotic-metrics question

The conjecture is false: there
exist a group $\Gamma$, a complete metric space $(M, d_1)$ on which $\Gamma$ acts, and a cocompact
asymptotically equivalent length-space pair on $M$ with second metric $d_2$, such that for every
real number $C$ there are points $x, y \in M$ with $|d_1(x, y) - d_2(x, y)| > C$.

Take the supremum product metric on $\mathbb{R}\times C_b(\mathbb{R},\mathbb{R})$, where $C_b$
is the space of bounded continuous functions with the supremum norm. This space is non-proper
because the closed unit ball in the infinite-dimensional function space is noncompact. Pull back
the product metric along $(t,f)\mapsto(t,b_t-f)$, where $b_t(r)=\sqrt{|r+t|}-\sqrt{|r|}$.
The common isometric action is transitive. From the origin to $(t,f)$ with $t\ge 0$ and $f$
constant with value $-t$, the two distances are $t$ and $t+\sqrt{t}$.

Counterexample of Le Donne, Nalon, Nicolussi Golo and Ryoo (arXiv:2503.00560, 2025), Example 4.2:
on the Engel group, a left-invariant Riemannian metric and its canonical asymptotic
sub-Riemannian metric are complete, left-invariant (transitive, hence cocompact), asymptotic,
yet their difference is unbounded.

## Sources

- E. Le Donne, L. Nalon, S. Nicolussi Golo, S.-Y. Ryoo, Asymptotics of Riemannian Lie groups with nilpotency step 2, arXiv preprint (2025), arXiv:2503.00560, https://arxiv.org/abs/2503.00560.
