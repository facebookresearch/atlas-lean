# One step of Hoppe's urn

For a real number $\theta$, an integer partition $\pi$ of $k$ with $a_j$ parts equal to $j$, and an integer partition $\pi'$ of $k + 1$, the transition weight from $\pi$ to $\pi'$ is the sum of

- $\theta/(\theta + k)$ if $\pi'$ is $\pi$ with one new part $1$ added, and $0$ otherwise, and
- for each part size $j$ of $\pi$, $j\, a_j/(\theta + k)$ if $\pi'$ is $\pi$ with one part $j$ replaced by $j + 1$, and $0$ otherwise,

with the convention that division by $0$ gives $0$. For $\theta > 0$, in Hoppe's urn the next gene carries a new allele with probability $\theta/(\theta + k)$ and copies an allele carried by $j$ genes with probability $j\, a_j/(\theta + k)$.

## Sources

- F. M. Hoppe, *Pólya-like urns and the Ewens sampling formula*, J. Math. Biol. 20 (1984), 91–94.
