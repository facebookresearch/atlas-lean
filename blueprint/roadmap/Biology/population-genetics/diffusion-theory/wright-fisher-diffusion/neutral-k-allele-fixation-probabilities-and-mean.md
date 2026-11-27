# The mean-time-to-monomorphism equation for neutral K-allele drift

For the neutral [K-allele generator](../wright-fisher-diffusion-with-selection-and-mutat/k-allele-wright-fisher-generator-on-the-simplex.md) without mutation, $L = \frac12 \sum_{i,j} x_i(\delta_{ij} - x_j)\partial_i\partial_j$, the function

$$T(x) = -2 \sum_{i=1}^K (1 - x_i) \log(1 - x_i) \qquad (x \in \Delta_{K-1},\ 0 \log 0 = 0)$$

satisfies $L T = -1$ in the relative interior of every face of dimension at least $1$ and $T = 0$ at the vertices. Indeed
$\partial_i \partial_j T = -2\delta_{ij}/(1 - x_i)$, so $L T = -\sum_i x_i = -1$, and on a face where only the alleles in $J$ are present $T$ is the
same formula over $J$. For $K = 2$ it is the [Kimura–Ohta mean absorption time](mean-absorption-time.md)
$-2(x \log x + (1 - x)\log(1 - x))$. Each coordinate $x_i$ is $L$-harmonic.

## Depends on

- [Generator of the K-allele Wright–Fisher diffusion with mutation and genic selection](../wright-fisher-diffusion-with-selection-and-mutat/k-allele-wright-fisher-generator-on-the-simplex.md)
- [Kimura–Ohta mean absorption time of a neutral allele](mean-absorption-time.md)

## Expansion

The identification of $T(x)$ with the expected time until one allele remains, and of $x_i$ with the fixation probability,
needs the $K$-allele diffusion as a process (existence, the strong Markov property and Dynkin's formula up to the
successive hitting times of faces); a sound expansion states that process and these two identities on their own pages.

## Sources

- M. Kimura and T. Ohta, "The average number of generations until fixation of a mutant gene in a finite population", Genetics 61 (1969), 763–771, <https://doi.org/10.1093/genetics/61.3.763> (two-allele case). The $K$-allele identity is derived above.
