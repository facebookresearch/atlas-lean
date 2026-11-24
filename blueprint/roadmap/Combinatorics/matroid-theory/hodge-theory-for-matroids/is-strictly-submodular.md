# Strictly submodular function

A real function $c$ on the nonempty proper subsets of the ground set $E$ is strictly
submodular if

$$c(I_1) + c(I_2) > c(I_1 \cap I_2) + c(I_1 \cup I_2)$$

for any two incomparable subsets $I_1, I_2 \subseteq E$, where $c(\emptyset)$ and
$c(E)$ are replaced by zero. Equivalently, $c$ is a real function on all subsets with $c(\emptyset) = c(E) = 0$ satisfying the strict inequality for incomparable $I_1, I_2 \subseteq E$; its values on sets not contained in $E$ play no role.

The rank function of a matroid, restricted to the nonempty proper subsets, is a limit of
strictly submodular functions. A strictly submodular function gives a strictly convex
piecewise linear function on the Bergman fan, that is, an ample class in the Chow ring.

## Sources

- K. Adiprasito, J. Huh and E. Katz, *Hodge theory for combinatorial geometries*, Ann. of
  Math. 188 (2018), 381–452, Section 1.2, https://arxiv.org/abs/1511.02888.
