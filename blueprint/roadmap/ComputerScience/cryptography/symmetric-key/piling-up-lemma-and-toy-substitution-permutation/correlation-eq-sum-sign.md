# Correlation eq sum sign

Let $p$ be a distribution on $\mathrm{Bool}$ and $s$ the [sign](../../../../Combinatorics/boolean-functions/kahn-kalai-linial-inequality/walsh-fourier-analysis-on-the-uniform-cube-and-t/khc-sign.md) map, $s(\mathrm{false}) = 1$ and $s(\mathrm{true}) = -1$. The [correlation](correlation.md) $\mathrm{corr}(p) = \mathrm{toReal}(p(\mathrm{false})) - \mathrm{toReal}(p(\mathrm{true}))$ is the signed sum over both bits:

$$
\mathrm{corr}(p) = \sum_{b \in \mathrm{Bool}} s(b) \cdot \mathrm{toReal}\bigl(p(b)\bigr).
$$
