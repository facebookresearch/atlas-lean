# Length-weighted flow through an oriented edge

For a [multicommodity flow](multicommodity-flow.md) $f$, the elongated flow through the oriented edge $e$ is $\bar f(e) = \sum_{p \ni e} f(p)\,|p|$, where $|p|$ is the number of edges of the path $p$ (A. Sinclair, *Combinatorics, Probability and Computing* 1 (1992), Section 4); $\bar\rho(f) = \max_e \bar f(e)/Q(e)$. Paths are counted with multiplicity, which for the simple paths of a flow is $0$ or $1$.
