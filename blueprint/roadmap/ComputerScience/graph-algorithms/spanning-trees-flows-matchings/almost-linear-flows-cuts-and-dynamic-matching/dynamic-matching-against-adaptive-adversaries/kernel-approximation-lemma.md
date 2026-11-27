# Deterministic (c, d, 0)-kernels preserve maximum matching within 2c(1+1/d)

If $H$ is a deterministic $(c, d, 0)$-kernel of $G$, then

$$
\mu(G) \le 2c\Bigl(1 + \frac{1}{d}\Bigr) \mu(H).
$$

## Proof sketch

Fix a maximum matching $M^\ast$ of $G$ and build a fractional matching of $H$: give every edge of $H$ value $1/d$, and additionally route $M^\ast$-edges missing from $H$ to the high-degree endpoint guaranteed by the kernel property. Degree bounds keep the vector feasible up to a $(1 + 1/d)$ factor, and its value is at least $\mu(G)/(2c)$ because each missing $M^\ast$-edge has an endpoint of $H$-degree at least $d/c$. Rounding within $H$ costs at most the fractional integrality factor, which an edge-colouring argument controls, giving the stated ratio.

## Depends on

- [Randomized (c, d, epsilon)-kernels for maximum matching](randomized-matching-kernels.md)
- [Fractional matchings and the fractional matching number](fractional-matching-number.md)

## Proof depends on

- [Proper edge coloring](../../../../../GraphTheory/graph-coloring/part-01/edge-coloring/is-proper-edge-coloring.md)

## Sources

- David Wajc, "Rounding Dynamic Matchings Against an Adaptive Adversary", STOC (2020), arXiv:1911.05545.
- Sayan Bhattacharya, Monika Henzinger, Giuseppe F. Italiano, "Deterministic Fully Dynamic Data Structures for Vertex Cover and Matching", SODA (2015), arXiv:1412.1318.
