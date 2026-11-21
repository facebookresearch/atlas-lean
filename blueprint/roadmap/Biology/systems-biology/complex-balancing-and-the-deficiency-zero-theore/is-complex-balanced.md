# Complex-balanced concentrations

Let $N$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with finite species set $S$ and finite reaction set $\rho$. Concentrations $c \in \mathbb{R}^S$ are complex balanced for rate constants
$k \in \mathbb{R}^\rho$ when, for every $z \in \mathbb{N}^S$, the total [mass-action rate](rate.md) of the
reactions with source complex $z$ equals the total rate of the reactions with product complex $z$:

$$\sum_{r \,:\, \mathrm{src}(r) = z} k_r \prod_{s} c_s^{\mathrm{src}(r)_s} = \sum_{r \,:\, \mathrm{prod}(r) = z} k_r \prod_{s} c_s^{\mathrm{src}(r)_s}.$$

For a vector $z$ that is the source or product of no reaction both sides are $0$.

## Sources

- F. Horn and R. Jackson, *General mass action kinetics*, Arch. Rational Mech. Anal. 47 (1972) 81–116.
- M. Feinberg, *Foundations of Chemical Reaction Network Theory*, Springer (2019), Chapter 15.
