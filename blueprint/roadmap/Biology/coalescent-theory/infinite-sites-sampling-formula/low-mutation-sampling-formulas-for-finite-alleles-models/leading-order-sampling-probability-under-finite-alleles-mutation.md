# Leading-order sampling probability under a finite-alleles mutation model

Consider Kingman's coalescent with a $K$-allele recurrent mutation model: mutations occur at population-scaled rate $\theta/2$ per lineage, and a mutation turns allele $j$ into allele $i$ with probability $P_{ji}$, where $\mathbf P$ is ergodic with stationary distribution $\pi$. For a sample configuration $\mathbf n = (n_1,\dots,n_K)$ of size $n = |\mathbf n|$, let $q(\mathbf n)$ be the stationary probability of any fixed ordered sample with that configuration. It is the unique solution of

$$n(n-1+\theta)\,q(\mathbf n) = \sum_i n_i(n_i-1)\,q(\mathbf n - \mathbf e_i) + \theta\sum_{i,j} P_{ji}\,n_i\,q(\mathbf n - \mathbf e_i + \mathbf e_j), \qquad q(\mathbf e_i) = \pi_i.$$

Let $\mathcal O = \{i : n_i > 0\}$ be the set of observed alleles and $O = |\mathcal O|$. If $\mathbf P$ restricted to $\mathcal O$ is irreducible, then

$$q(\mathbf n) = \theta^{O-1}\,\tilde q(\mathbf n) + O(\theta^{O}), \qquad \Lambda(\mathbf n) := \frac{\prod_{i\in\mathcal O}(n_i - 1)!}{(n-1)!},$$

where $\tilde q(\mathbf n)$ depends on $\mathbf P$ but not on $\theta$: it is the total probability of genealogies carrying the parsimonious number $O - 1$ of mutations.

**Theorem.**

1. If $O = 1$, $\mathbf n = n\mathbf e_i$, then $\tilde q(\mathbf n) = \pi_i$.
2. If $O = 2$ and $\mathbf P$ is irreducible on $\mathcal O$, then

$$\tilde q(\mathbf n) = \Lambda(\mathbf n)\sum_{i\ne j\in\mathcal O}\frac{n_j}{n}\,\pi_j P_{ji}.$$

3. If $O = 3$ with observed alleles $a,b,c$ and $\mathbf P$ is reversible ($\pi_i P_{ij} = \pi_j P_{ji}$) and irreducible on $\mathcal O$, then

$$\tilde q(\mathbf n) = \Lambda(\mathbf n)\Big(\frac{n_a}{n}\pi_a P_{ab}P_{ac} + \frac{n_b}{n}\pi_b P_{ba}P_{bc} + \frac{n_c}{n}\pi_c P_{ca}P_{cb}\Big).$$

For $O = 3$ with arbitrary irreducible $\mathbf P$, and for $O = 4$ with reversible irreducible $\mathbf P$, $\tilde q(\mathbf n)$ is again $\Lambda(\mathbf n)$ times an explicit finite combination of products $\pi_i P_{ij}P_{ik}\cdots$ with rational coefficients in the $n_i$ and harmonic numbers $H_n - H_{m}$. The formula of item 3, known earlier for mutation that is parent-independent on $\mathcal O$, thus holds for reversible $\mathbf P$ when $O \le 3$; for $O = 4$ it fails unless $\mathbf P$ is parent-independent on $\mathcal O$.

## Depends on

- [Time to the most recent common ancestor under Kingman's coalescent](../../kingman-s-coalescent-and-watterson-s-estimator/tmrca.md)

## Expansion

Unwinding the recursion, each mutation contributes a factor $\theta$, so only genealogies with exactly $O-1$ mutations contribute at order $\theta^{O-1}$, one mutation creating each non-ancestral observed type. The proof builds an urn process related to the coalescent: the leading coefficient decomposes as a sum over mutation trees on $\mathcal O$ of a $\mathbf P$-dependent product times a purely combinatorial probability, and a martingale property of the urn gives that probability. Writing $\tilde q = \Lambda(\mathbf n)\,\tilde r(\mathbf n)$ yields a recursion for $\tilde r$ that is solved combinatorially for $O \le 4$.

## Sources

- Anand Bhaskar, John A. Kamm, Yun S. Song, "Approximate sampling formulae for general finite-alleles models of mutation", *Advances in Applied Probability* 44 (2012), 408–428, <https://doi.org/10.1239/aap/1339878718>; preprint arXiv:1109.2386, <https://doi.org/10.48550/arXiv.1109.2386>. Numbering of the arXiv version: Section 2 (model, recursion, expansion, $\Lambda$), Section 3 (closed forms for $O = 2, 3, 4$ and the reversible $O = 3$ corollary), Section 4 (urn construction and recursion for $\tilde r$).
