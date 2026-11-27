# Sample covariance of the centred genotype matrix

For a real matrix $Z$ indexed by samples $\iota$ (finite) and loci $S$ (finite, $L = |S|$), the sample covariance of samples $i, j$ is

$$C_{ij} = \frac{1}{L} \sum_{s \in S} X_{is} X_{js},$$

where $X$ is the [column-centred matrix](centered.md), with the convention $x/0 = 0$.
