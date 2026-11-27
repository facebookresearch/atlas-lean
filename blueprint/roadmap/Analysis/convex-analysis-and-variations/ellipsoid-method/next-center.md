# Centre after a central-cut step

The new centre of the central-cut step in dimension $n$ is $a' = a - \frac{1}{n+1}\, b$, where $b = A c / \sqrt{c^\top A c}$ is the [cut direction](cut-direction.md): the centre moves from $a$ by a fraction $1/(n+1)$ of the way towards the far side of the half-ellipsoid $E(a, A) \cap \{c^\top x \le c^\top a\}$.

## Sources

- M. X. Goemans, *Lecture notes on the ellipsoid algorithm*, MIT 18.433 Combinatorial Optimization, Handout 19 (4 May 2009), <https://math.mit.edu/~goemans/18433S09/ellipsoid.pdf>, equation (5) and step 2 of the algorithm.
