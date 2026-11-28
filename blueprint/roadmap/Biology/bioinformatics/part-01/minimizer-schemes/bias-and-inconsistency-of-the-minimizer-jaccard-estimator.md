# Bias and inconsistency of the minimizer Jaccard estimator

Let $k \ge 2$, $w \ge 2$ and $L \ge 7(w+1)$ be integers, and let $A$ and $B$ be duplicate-free sequences (no $k$-mer occurs twice in the same sequence), each consisting of $L$ $k$-mers $A_0, \dots, A_{L-1}$ and $B_0, \dots, B_{L-1}$. With $\mathrm{Sp}_k(\cdot)$ the set of $k$-mers, the Jaccard similarity is

$$J(A,B) = \frac{|\mathrm{Sp}_k(A) \cap \mathrm{Sp}_k(B)|}{|\mathrm{Sp}_k(A) \cup \mathrm{Sp}_k(B)|}.$$

Let a hash $h$ assign to every $k$-mer an independent uniform value in $[0,1]$, and let the minimizer sketch be

$$\mathrm{MS}(A;w) = \bigcup_{i=0}^{L-w} \Bigl\{A_p : p = \arg\min_{j \in [i, i+w-1]} h(A_j)\Bigr\}.$$

The minimizer Jaccard estimator is $\hat J(A,B;w) = J\bigl(\mathrm{MS}(A;w), \mathrm{MS}(B;w)\bigr)$, the Jaccard similarity of the two sketches. Call $A, B$ *padded* if they share no minimizer among their first or last $w$ $k$-mers, and *sparsely matched* if they are padded and, whenever $A_p = B_q$, none of $A_{p-w}, \dots, A_{p+w}$ other than $A_p$ occurs in $B$ and none of $B_{q-w}, \dots, B_{q+w}$ other than $B_q$ occurs in $A$.

1. **Bias formula.** There is a deterministic quantity $\mathcal B(A,B;w)$, a function of $w$, $L$ and the matching of shared $k$-mers between positions of $A$ and $B$, and some $\varepsilon \in [0, 15 w^2 / L^{1/3}]$, such that

    $$\mathcal B(A,B;w) - \varepsilon \le \mathbb E[\hat J(A,B;w)] - J(A,B) \le \mathcal B(A,B;w) + \varepsilon .$$

2. **Sign.** For padded $A, B$: $\mathcal B(A,B;w) < 0$ unless $J(A,B) = 0$, in which case $\mathcal B = 0$.
3. **Sparse matches.** For sparsely matched $A, B$:

    $$\mathcal B(A,B;w) \le -J(A,B)\,\frac{3w^2 - 3w}{8w^2 - 2}, \qquad\text{hence}\qquad \frac{\mathbb E[\hat J]}{J} \le \frac{5w^2 + 3w - 2}{8w^2 - 2} + \frac{\varepsilon}{J}\ \ (J > 0).$$

So $\hat J$ is biased downward, and for a fixed true $J > 0$ the ratio $\mathbb E[\hat J]/J$ stays at most $(5w^2 + 3w - 2)/(8w^2 - 2) < 1$ as $L \to \infty$ (this bound decreases to $5/8$ as $w$ grows): the estimator is inconsistent. At $w = 2$ the bound is $0.8$ and at $w = 20$ about $0.64$. The source's corollary prints the numerator as $5w^2 - 3w - 2$, which does not follow from its bias bound.

## Depends on

- [Expected density of random-order minimizers](../../../../ComputerScience/string-algorithms/winnowing-and-minimizers/winnowing-minimizer-density-2-w-1-and-the-1-5-w-1-lower-bound-for-loca.md)

## Expansion

$\hat J$ depends on how the shared $k$-mers are laid out along the two sequences, whereas $J$ depends only on their number. For $w = 2$ and a shared $k$-mer with hash $a_1$, being a minimizer in both sequences is an event about the order of five independent hashes when its neighbours differ ($\tau = 64/120$) but of four hashes when one neighbour is also shared ($\tau = 14/24$), at the same $J$. The proof writes the expected sketch intersection as $\mathbb E[\hat I] = \sum_{p,q} \mathbb P[A_p \text{ and } B_q \text{ both minimizers}]$, approximated within $2$ by an explicit combinatorial term $C(A,B;w)$. The expected sketch union is $4L/(w+1) - C$ up to $10$, since each sketch has about $2L/(w+1)$ elements. The variance bounds $\mathrm{Var}(\hat I) \le 8w^2 I(A,B)$ and $\mathrm{Var}(\hat U) \le 32 w^2 L$, together with Chebyshev's inequality, show $\mathbb E[\hat I/\hat U]$ is within $11 w^2/L^{1/3}$ of $\mathbb E[\hat I]/\mathbb E[\hat U]$. Hence $\mathbb E[\hat J] \approx C/(4L/(w+1) - C)$, and $\mathcal B$ is that ratio minus $J$. For identical sequences except for a mutation every $g > w + 2k$ positions, $\mathcal B$ has a closed form involving harmonic numbers, giving about a $10\%$ underestimate at $k = 15$, $w = 10$, $g = 43$. In read mapping the bias led to sequence-divergence estimates off by up to $14\%$.

## Sources

- M. Belbasi, A. Blanca, R. S. Harris, D. Koslicki, P. Medvedev, "The minimizer Jaccard estimator is biased and inconsistent", *Bioinformatics* (2022), Section 2 (definitions), Section 3 (Theorems 1–4) and Section 4 (Lemmas 1–5), <https://doi.org/10.1093/bioinformatics/btac244> (PMC9235516).
