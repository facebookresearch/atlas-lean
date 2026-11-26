# Large-population fixation probability in a heterogeneous environment

In the [Moran process with environment-dependent fitness](moran-process-with-environment-dependent-fitness.md), fix the number $m$ of environments and suppose $N_i(N)/N \to p_i \in (0,1)$ as $N \to \infty$ for each $i$. Let $f$ be the limiting distribution of the mutant rate (mass $p_i$ at $a_i$), $g$ that of the resident rate, $\bar a = \sum_i p_i a_i$ and $\bar b = \sum_i p_i b_i$. Then $\rho_A^\infty(f,g) = \lim_{N\to\infty}\rho_A^N(f_N,g_N)$ exists and satisfies

$$\rho_A^\infty(f,g) = 0 \quad \text{if } \bar a \le \bar b, \qquad \mathbb{E}_f\!\left[\frac{a}{\bar b + a\,\rho_A^\infty(f,g)}\right] = 1 \quad \text{if } \bar a > \bar b,$$

where $\mathbb{E}_f$ averages over the mutant rate $a \sim f$.

Consequences:

- **Neutrality and direction of selection.** $\rho_A^\infty(f,g) = \rho_A^\infty(g,f)$ iff $\bar a = \bar b$; $A$ is favoured over $B$ iff $\bar a > \bar b$. In large populations only the spatial mean rates decide which type selection favours.
- **Resident heterogeneity is invisible.** The resident distribution enters only through $\bar b$, so $\rho_A^\infty(f,g) = \rho_A^\infty(f,\bar b)$.
- **Homogeneous check.** If $f$ is a point mass at $\bar a > \bar b$, the equation gives $\rho_A^\infty = 1 - \bar b/\bar a$, the large-$N$ limit of the classical Moran fixation probability.

## Depends on

- [Moran process with environment-dependent fitness](moran-process-with-environment-dependent-fitness.md)
- [Fixation probability of the Moran process](../moran-fixation.md)

## Proof depends on

- [Absorption probabilities and mean times of a finite Markov chain](../../../../Probability/markov-chains/finite-markov-chains/absorption-probabilities-and-mean-absorption-tim.md)

## Expansion

When $\bar a > \bar b$ the function $\Psi(\rho) = \mathbb{E}_f[a/(\bar b + a\rho)]$ is continuous and strictly decreasing on $[0,1]$, with $\Psi(0) = \bar a/\bar b > 1$ and $\Psi(1) = \mathbb{E}_f[a/(\bar b + a)] < 1$, so the equation has a unique root in $(0,1)$. Heuristically, while mutants are rare a mutant with rate $a$ reproduces at rate proportional to $a$ and dies at rate proportional to $\bar b$, and its offspring land in an environment drawn from $f$. If $s(a)$ is the survival probability of such a branching lineage and $\bar s = \mathbb{E}_f[s]$, first-step analysis gives $s(a) = \frac{a}{a + \bar b}\,[1 - (1 - s(a))(1 - \bar s)]$, i.e. $s(a) = a\bar s/(\bar b + a\bar s)$; averaging over $a \sim f$ yields the displayed equation with $\rho_A^\infty = \bar s$. The derivation in the source (Eq. (2.6) and Appendix A) solves the absorption equations of the finite chain and takes $N \to \infty$.

## Sources

- K. Kaveh, A. McAvoy, M. A. Nowak, "Environmental fitness heterogeneity in the Moran process", Royal Society Open Science (2019), Section 2.2, Eq. (2.6), and Appendix A, <https://doi.org/10.1098/rsos.181661> (PMC6366185).
