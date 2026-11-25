# Diffuse enclosure: areas, view factors, row sums and reciprocity

For a finite set `ι` of surfaces, areas `A : ι → ℝ` and view factors `F : ι × ι → ℝ` (`F_{ij}` the
fraction of the radiation leaving `i` that arrives at `j`) form a black enclosure when:

- `A_i > 0` for every surface;
- `F_{ij} ≥ 0` for all surfaces;
- `∑_j F_{ij} = 1` for every surface `i` (closure: an opening must be an explicit surface);
- `A_i F_{ij} = A_j F_{ji}` for all surfaces (reciprocity).

The same conditions are used for gray enclosures, whose surfaces also carry emissivities.
