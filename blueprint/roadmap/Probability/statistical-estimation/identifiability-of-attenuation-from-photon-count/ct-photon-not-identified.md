# One ray through two cells does not identify a nonnegative attenuation

For every nonnegative source intensity $I_0$, the map sending an attenuation vector
$x \in \mathbb{R}^2$ to the [photon-count law](photon-law.md) of the [single-ray design](ct-row.md)
is not injective on the set of vectors with nonnegative entries: the distinct vectors $(1, 0)$ and
$(1, 0) + (-1, 1) = (0, 1)$ are both nonnegative and have the same law, since $(-1, 1)$ lies in the
kernel of the design.
