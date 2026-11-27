# First-order multi-locus sampling formula in inverse recombination rate

Consider $L$ linked loci under the coalescent with recombination: locus $l$ has $K_l$ alleles, mutation rate $\theta_l$ and mutation matrix $P^{(l)}$ (any finite-alleles model; the result also holds for infinite alleles), and recombination between loci $l$ and $l+1$ occurs at rate $\rho_l = r_l\rho$. A **haplotype** $h$ assigns to each locus an allele or the unspecified symbol $\circ$ (not all unspecified); $S(h)$ is the set of specified loci. A sample is $\mathbf n = (n_h)_h$ and $q(\mathbf n)$ its stationary sampling probability (for one fixed ordering); $\mathbf n^{(l)}$ is the marginal sample at locus $l$ and $q^{(l)}$ the one-locus sampling distribution. For a set of loci $X$ let $r(X) = r_{\min X} + \dots + r_{\max X - 1}$, and for a haplotype $h$ (or $h = \circ^L$) let $H(h,X)$ be the haplotypes specified at least on $X$ that agree with $h$ on $S(h)$.

Because $q(\mathbf n)$ solves a finite linear system with entries linear in $\rho$, it is a rational function of $\rho$ bounded as $\rho \to \infty$, so

$$q(\mathbf n) = q_0(\mathbf n) + \frac{q_1(\mathbf n)}{\rho} + \frac{q_2(\mathbf n)}{\rho^2} + O(\rho^{-3}).$$

**Proposition (zeroth order).** $q_0(\mathbf n) = \prod_{l=1}^L q^{(l)}(\mathbf n^{(l)} \mid \theta_l, P^{(l)})$: with infinite recombination the loci are independent.

**Theorem (first order).** $q_1$ is the unique solution of an inclusion–exclusion recursion with $q_1(\mathbf e_h) = 0$, and

$$q_1(\mathbf n) = \sum_{h \in \mathcal H \cup \{\circ^L\}} q_0(\mathbf n - \mathbf e_h) \sum_{\substack{X \supseteq S(h)\\ |X| \ge 2}} \frac{(-1)^{|X - S(h)|}}{r(X)}\binom{\sum_{h' \in H(h,X)} n_{h'}}{2},$$

where $q_0(\mathbf n - \mathbf e_h)$ is the product of marginal one-locus probabilities after removing one copy of $h$ (and is $q_0(\mathbf n)$ for $h = \circ^L$). Hence

$$q(\mathbf n) = \prod_l q^{(l)}(\mathbf n^{(l)}) + \frac{q_1(\mathbf n)}{\rho} + O(\rho^{-2}).$$

The mutation model enters only through the one-locus marginals (for parent-independent mutation, Wright's formula; for infinite alleles, the Ewens sampling formula), so the first two terms are universal. For $L = 2$ the formula reduces to the Jenkins–Song two-locus result.

## Expansion

At infinite $\rho$ every haplotype shatters into single-locus fragments that coalesce independently, giving the product form. Substituting the expansion into the coalescent-with-recombination recursion and collecting the $\rho^0$ terms gives a recursion for $q_1$ driven only by recombination splits on the left and by coalescences among fragments on the right; inclusion–exclusion over which loci a pair of lineages still shares turns the right-hand side into the signed sums over $X \supseteq S(h)$. The closed form is verified to solve this recursion by a direct combinatorial argument (equivalently, via Wallenius noncentral hypergeometric probabilities for the order in which shared segments are broken): the weight $1/r(X)$ is the expected time a pair sharing the loci $X$ stays linked before recombination separates them.

## Sources

- Anand Bhaskar, Yun S. Song, "Closed-form asymptotic sampling distributions under the coalescent with recombination for an arbitrary number of loci", *Advances in Applied Probability* 44 (2012), 391–407, <https://doi.org/10.1239/aap/1339878717>; preprint arXiv:1107.4700, <https://doi.org/10.48550/arXiv.1107.4700>. Numbering of the arXiv version: Section 2 (model and notation), Section 3 (recursion and expansion, Proposition on $q_0$, Proposition on the $q_1$ recursion, Theorem on $q_1$, Corollary), Section 4 (three-locus case and reduction to two loci).
