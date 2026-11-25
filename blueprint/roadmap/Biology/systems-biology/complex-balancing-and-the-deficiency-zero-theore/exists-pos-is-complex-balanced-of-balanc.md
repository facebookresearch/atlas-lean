# At deficiency zero, positive balancing weights give complex balance

Let $N$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
finite species set $S$ and finite reaction set $\rho$, and suppose that $N$ has deficiency zero in
the [linear form](deficiency-eq-zero-iff.md): whenever $\alpha \in \mathbb{R}^\rho$ satisfies
$\sum_{r} \alpha_r (\mathrm{prod}(r) - \mathrm{src}(r)) = 0$ in $\mathbb{R}^S$, every function
$\eta \colon \mathbb{N}^S \to \mathbb{R}$ satisfies

$$\sum_{r \in \rho} \alpha_r \bigl(\eta(\mathrm{prod}(r)) - \eta(\mathrm{src}(r))\bigr) = 0.$$

Let $k \in \mathbb{R}^\rho$ be rate constants of any sign, and let
$\psi \colon \mathbb{N}^S \to \mathbb{R}$ be positive at every
[complex](../../../Dynamics/smooth-dynamics/complexes.md) of $N$ and balance the $k$-weighted
reaction graph: at every $z \in \mathbb{N}^S$ the outflow equals the inflow,

$$\psi(z) \sum_{\mathrm{src}(r) = z} k_r = \sum_{\mathrm{prod}(r) = z} k_r \psi(\mathrm{src}(r)).$$

Then some $c \in \mathbb{R}_{>0}^S$ is [complex balanced](is-complex-balanced.md) for $k$. In the
chemical model the rate constants are positive; the statement holds for all real $k$.

The proof, Horn's construction, takes $c_s = e^{\mu_s}$, where $\mu \in \mathbb{R}^S$ is chosen so
that, for every reaction $r$, the dot product of $\mathrm{prod}(r) - \mathrm{src}(r)$ with $\mu$
equals $\log \psi(\mathrm{prod}(r)) - \log \psi(\mathrm{src}(r))$; the deficiency hypothesis makes
this linear system solvable. Then $c^y / \psi(y)$, where $c^y = \prod_s c_s^{y_s}$, has the same
value at both ends of every reaction, and complex balance follows from the balance of $\psi$.

## Sources

- F. Horn, *Necessary and sufficient conditions for complex balancing in chemical kinetics*,
  Arch. Rational Mech. Anal. 49 (1972) 172–186.
- M. Feinberg, *Foundations of Chemical Reaction Network Theory*, Springer (2019), Chapter 16.
