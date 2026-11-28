# Excursion formula for the Perron-Frobenius eigenvector of a mutation-selection matrix

Let $A$ be a non-negative primitive $N \times N$ matrix with Perron-Frobenius eigenvalue $\lambda > 0$ and left Perron-Frobenius eigenvector $u$ normalized to the unit simplex, $u^\top A = \lambda u^\top$, $\sum_i u_i = 1$. Write $A(i,j) = f(i) M(i,j)$, where $f(i) = \sum_j A(i,j) > 0$ is the $i$-th row sum and $M = (A(i,j)/f(i))$ is a primitive stochastic matrix. Let $(X_n)_{n \ge 0}$ be the Markov chain on $\{1, \dots, N\}$ with transition matrix $M$, let $E_k$ denote expectation for the chain started at $k$, and let $\tau_k = \inf\{n \ge 1 : X_n = k\}$ be the first return time to $k$.

**Theorem.** For every $1 \le k \le N$ and every $i$,

$$ u_i = \frac{E_k\Bigl( \sum_{n=0}^{\tau_k - 1} 1_{\{X_n = i\}}\, \lambda^{-n} \prod_{t=0}^{n-1} f(X_t) \Bigr)}{E_k\Bigl( \sum_{n=0}^{\tau_k - 1} \lambda^{-n} \prod_{t=0}^{n-1} f(X_t) \Bigr)}. $$

**Corollary.** For every $k$, $u_k = 1 \big/ E_k\Bigl( \sum_{n=0}^{\tau_k - 1} \lambda^{-n} \prod_{t=0}^{n-1} f(X_t) \Bigr)$. When $A$ is stochastic ($f \equiv 1$, $\lambda = 1$) this is Kac's formula $u_k = 1/E_k(\tau_k)$ for the invariant probability of an ergodic chain.

**Mutation-selection interpretation.** If type $i$ reproduces at rate $f(i)$, offspring of type $i$ mutate to type $j$ with probability $M(i,j)$, and death rates do not depend on type, then the equilibrium type frequencies $x$ solve $x_k \sum_i x_i f(i) = \sum_i x_i f(i) M(i,k)$ for all $k$. Their unique solution in the simplex is $u$, and $\lambda = \sum_i u_i f(i)$ is the mean fitness at equilibrium. The chain $X$ is the lineage of a mutant in a neutral population ($f \equiv 1$), and the formula expresses the equilibrium of the selective model as a fitness-weighted occupation measure of neutral excursions. The same $u$ is the limiting type distribution, conditioned on survival, of a supercritical multitype Galton-Watson process with mean matrix $A$.

## Depends on

- [Perron–Frobenius theorem for primitive nonnegative matrices](../../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius-for-primitive-nonnegative-matri.md)
- [Normalized growth of supercritical multitype Galton–Watson processes](../../../../Probability/branching-processes/galton-watson-process/normalized-growth-of-multitype-galton-watson-pro.md)

## Expansion

The key identity (Lemma) is the expansion of $1$ along excursions from $k$: for any $k$,

$$ 1 = \sum_{n \ge 1} \lambda^{-n} \sum_{i_1, \dots, i_{n-1} \neq k} A(k, i_1) A(i_1, i_2) \cdots A(i_{n-1}, k), $$

that is, $E_k\bigl(\lambda^{-\tau_k} \prod_{t=0}^{\tau_k - 1} f(X_t)\bigr) = 1$. It follows by decomposing the Perron eigenvector equation into first-return paths, using that the spectral radius of $A$ restricted to the complement of $\{k\}$ is strictly smaller than $\lambda$, so that the series converges. Defining $v_i$ as the numerator in the theorem, a first-step (renewal) argument shows that $v^\top A = \lambda v^\top$; since $v$ is non-negative and nonzero it is a multiple of $u$ by the Perron-Frobenius theorem, and dividing by $\sum_i v_i$ normalizes it. Taking $i = k$ gives the corollary because only the time $n = 0$ of the excursion visits $k$.

## Sources

- Raphaël Cerf and Joseba Dalmau, *A Markov chain representation of the normalized Perron–Frobenius eigenvector*, Electron. Commun. Probab. 22 (2017), 1–6. <https://doi.org/10.1214/17-ECP76> Theorem, Corollary and Lemma of the main section; mutation-selection and multitype Galton–Watson applications. Locators use the preprint, titled *A Markov chain representation of the Perron-Frobenius eigenvector*, arXiv:1607.01127.
