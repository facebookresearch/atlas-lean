# Moment duality between the two-locus Wright–Fisher diffusion and the ancestral process with recombination

Consider two linked biallelic loci with alleles $A_1, A_2$ and $B_1, B_2$ in a random-mating diploid population of size $N$, with recombination fraction $r$ and scaled recombination rate $\rho = 4Nr$ held fixed while time is measured in units of $2N$ generations. Let $x_1$ be the frequency of the gamete $A_1B_1$, $x$ and $y$ the frequencies of $A_1$ and $B_1$, and $z$ the linkage disequilibrium $z = x_1 x_4 - x_2 x_3$ (with $x_2, x_3, x_4$ the frequencies of $A_1B_2$, $A_2B_1$, $A_2B_2$). The diffusion $(x(t), y(t), z(t))$ has the Ohta–Kimura generator

$$\mathcal L = \tfrac{x(1-x)}{2}\partial_x^2 + \tfrac{y(1-y)}{2}\partial_y^2 + z\,\partial_x\partial_y + z(1-2x)\,\partial_x\partial_z + z(1-2y)\,\partial_y\partial_z - z\big(1 + \tfrac\rho2\big)\partial_z + \tfrac12\big\{xy(1-x)(1-y) + z(1-2x)(1-2y) - z^2\big\}\partial_z^2.$$

In a section at time $t$ (backwards) of the two-locus ancestral recombination graph of a sample, let $a(t)$, $b(t)$, $c(t)$ be the numbers of lineages ancestral at locus $A$ only, at locus $B$ only, and at both loci. Then $(a,b,c)$ is a Markov chain on $\mathbb Z_+^3\setminus\{\mathbf 0\}$ with transition rates (while $a + b + c > 1$)

$$(a,b,c) \to (a+1,b+1,c-1) \text{ at rate } \tfrac{c\rho}{2}, \quad (a-1,b-1,c+1) \text{ at rate } ab, \quad (a-1,b,c) \text{ at rate } ac + \tfrac{a(a-1)}{2},$$

$$(a,b-1,c) \text{ at rate } bc + \tfrac{b(b-1)}{2}, \quad (a,b,c-1) \text{ at rate } \tfrac{c(c-1)}{2}.$$

**Theorem (moment duality).** If $(x(0), y(0), x_1(0)) = (p, q, g)$ and $(a(0), b(0), c(0)) = (l, m, n)$, then for all $t \ge 0$

$$\mathbb E_{p,q,g}\big[x(t)^l\,y(t)^m\,x_1(t)^n\big] = \mathbb E_{l,m,n}\big[p^{a(t)}\,q^{b(t)}\,g^{c(t)}\big].$$

Both sides solve the same backward system

$$\tfrac{d\xi_{l,m,n}}{dt} = -\tfrac{(l+m+n)(l+m+n-1) + n\rho}{2}\,\xi_{l,m,n} + \tfrac{n\rho}{2}\,\xi_{l+1,m+1,n-1} + \tfrac{l(l-1+2n)}{2}\,\xi_{l-1,m,n} + \tfrac{m(m-1+2n)}{2}\,\xi_{l,m-1,n} + \tfrac{n(n-1)}{2}\,\xi_{l,m,n-1} + lm\,\xi_{l-1,m-1,n+1}.$$

The chain is absorbed in $\mathcal S = \{(1,1,0), (0,0,1)\}$, the states in which the sample has found its common ancestor at both loci; writing $W_A$, $W_B$ for the two marginal TMRCAs, $\mathbb P_{l,m,n}[W_A \vee W_B \le t] = \mathbb P_{l,m,n}[(a(t),b(t),c(t))\in\mathcal S]$.

## Depends on

- [Two-locus ancestral process for n sequences](../two-locus-ancestral-process-for-n-sequences.md)
- [Generator of the two-locus Wright–Fisher diffusion](../two-locus-generator.md)

## Expansion

A lineage of type $A$-only carries a factor $x$, $B$-only a factor $y$, and a doubly ancestral lineage a factor $x_1$ (both alleles of type 1 on the same gamete). Applying $\mathcal L$ to $x^l y^m x_1^n$ and regrouping produces exactly the rate-weighted differences of the right-hand chain: a recombination splits $x_1$ into $x\cdot y$, an $A$-only/$B$-only coalescence fuses them into $x_1$, and same-type coalescences reduce a power. Since both sides satisfy the same linear system with the same initial values, they agree; the proof also yields an unbiased Monte Carlo estimator of $\mathbb E[x^l y^m x_1^n]$ by simulating the chain up to $t\wedge\tau$, where $\tau$ is the absorption time.

## Sources

- Shuhei Mano, "Duality between the two-locus Wright–Fisher diffusion model and the ancestral process with recombination", *Journal of Applied Probability* 50 (2013), 256–271, <https://doi.org/10.1239/jap/1363784437>; preprint arXiv:1201.5557, <https://doi.org/10.48550/arXiv.1201.5557>. Numbering of the arXiv version: Section 2 (generator), Section 3 (transition rates, backward system, Lemma 3.1, Proposition 3.2), Proposition 5.1.
