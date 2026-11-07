# Local alignment score

For an integer substitution score $\sigma$, an integer gap score
$g$ and sequences $x$ and $y$, the local score of $x$ and $y$ is the maximum of the
Needleman–Wunsch score of $(x', y')$ over all pairs of an infix $x'$ of $x$ and an infix $y'$ of
$y$ (contiguous and possibly empty).
