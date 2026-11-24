# Near-orthogonality of disjointly supported sparse vectors

Let $\iota$ be a finite index set, $\Phi \in \mathbb{R}^{m \times \iota}$ and $s, s' \in \mathbb{N}$,
and suppose $\Phi$ has the [restricted isometry property](has-rip.md) of order $s + s'$ with
constant $\delta$. If $x, x' \in \mathbb{R}^\iota$ are supported on disjoint sets $T$, $T'$ with
$|T| \le s$ and $|T'| \le s'$, then

$$|\langle \Phi x, \Phi x'\rangle| \le \delta\, \|x\|_2\, \|x'\|_2 .$$

## Sources

- E. J. Candès, *The restricted isometry property and its implications for compressed sensing*, C. R. Acad. Sci. Paris, Ser. I 346 (2008) 589–592, Lemma 2.1
