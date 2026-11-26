# Extended polynomials

The *extended polynomials* form the smallest class of functions $\mathbb{N}^k \to \mathbb{N}$, $k \ge 0$, that contains

- the constant functions $0$ and $1$,
- the projections $(n_1, \dots, n_k) \mapsto n_i$ for $1 \le i \le k$,
- addition $(n, m) \mapsto n + m$ and multiplication $(n, m) \mapsto n \cdot m$,
- the conditional $\mathrm{ifzero}(n, m, p)$, equal to $m$ if $n = 0$ and to $p$ otherwise,

and is closed under composition: if $g : \mathbb{N}^j \to \mathbb{N}$ and $h_1, \dots, h_j : \mathbb{N}^k \to \mathbb{N}$ are extended polynomials, so is
$\vec n \mapsto g(h_1(\vec n), \dots, h_j(\vec n))$. So the extended polynomials are the polynomials with natural-number coefficients, closed under the
conditional; for example the signum function is $\mathrm{ifzero}(n, 0, 1)$ and $n \mapsto 2n$ is $n + n$.

Closure under composition, which identifies and permutes arguments, is part of the definition. A variant that closes the base functions only
under sum and product on disjoint argument lists, as in Definition 3.5.5 of the Sørensen–Urzyczyn notes, is too small: its unary members are only the
identity, the constants and the signum, so it misses the λ→-definable function $n \mapsto 2n$.

## Sources

- M. Zakrzewski, "Definable functions in the simply typed λ-calculus", arXiv:cs/0701022v1, 2007, <https://arxiv.org/abs/cs/0701022v1>: Section 1.1, Definition 1.
- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Definition 3.5.5, which lists the same base functions but omits closure under composition.
