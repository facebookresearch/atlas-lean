# Eigenvalue effective size from the gene diversity recursion

**Setting.** A population is divided into $s$ subpopulations with sizes $2Nu_i$ genes, $\sum_i u_i = 1$, and a biallelic gene evolves in discrete generations without mutation; $X_t = (X_t^1, \dots, X_t^s)$ are the subpopulation allele frequencies, a finite Markov chain on a state space $\mathcal{X}$ with transition matrix $P$. Partition $\mathcal{X}$ into the two fixation states $\mathcal{X}_1 = \{(0,\dots,0)\}$, $\mathcal{X}_2 = \{(1,\dots,1)\}$ and components $\mathcal{X}_3, \dots, \mathcal{X}_n$, ordered so that $P$ is block lower triangular with diagonal blocks $P_{11} = P_{22} = 1$ and $P_{33}, \dots, P_{nn}$. Assume that each $P_{ii}$, $i = 3, \dots, n$, is irreducible and aperiodic with at least one row sum less than $1$. Then the eigenvalues of $P$ can be ordered as $1 = \lambda_1 = \lambda_2 > \lambda_3 \ge |\lambda_4| \ge \cdots \ge 0$, with $\lambda := \lambda_3(P) = \max_{3 \le i \le n} \lambda_{\max}(P_{ii})$. Since the Wright–Fisher model with $N$ diploids has $\lambda_3 = 1 - 1/(2N)$, the **eigenvalue effective size** is defined by

$$N_{eE} = \frac{1}{2(1 - \lambda)}.$$

If moreover the maximum is attained at a unique $k$, and $\phi \colon \mathcal{X} \to \mathbb{R}$ vanishes on $\mathcal{X}_1 \cup \mathcal{X}_2$, is $\ge 0$ on the other components and $> 0$ on $\mathcal{X}_k$, then $\lim_{t \to \infty} \lambda^{-t}\,\mathbb{E}_\pi \phi(X_t)$ exists and is finite, and it is strictly positive whenever the initial distribution $\pi$ gives $\mathcal{X}_k$ positive mass. In particular ($\phi = \mathbf{1}\{x \notin \mathcal{X}_1 \cup \mathcal{X}_2\}$), the probability of non-fixation decays at rate $\lambda^t$.

**Gene diversity.** Let $H_t^{ij} = X_t^i(1 - X_t^j) + X_t^j(1 - X_t^i)$ be the probability that genes drawn from subpopulations $i$ and $j$ differ, and $\mathbf{H}_t = (\mathbb{E}_\pi H_t^{ij})_{i,j}$ the vector of predicted gene diversities.

**Theorem.**
1. Under the assumptions of the Setting, if $\mathbf{H}_t = A\,\mathbf{H}_{t-1}$ for a nonnegative $s^2 \times s^2$ matrix $A$, then $\lambda_3(P) = \lambda_{\max}(A) = \max_a \lambda_{\max}(A_{aa})$ over the irreducible diagonal blocks of a block lower-triangular form of $A$, and hence

$$N_{eE} = \frac{1}{2\,(1 - \lambda_{\max}(A))}.$$

2. Such a recursion holds whenever the backward subpopulation ancestry of two distinct genes before coalescence is a Markov chain with transition matrix $Q = (Q_{ij,kl})$ on pairs of subpopulations. Let $\nu_{ki}$ be the number of offspring in subpopulation $i$ of one gene of subpopulation $k$ in the previous generation, $V_{kii} = \mathbb{E}[\nu_{ki}(\nu_{ki} - 1)]$ and $V_{kij} = \mathbb{E}[\nu_{ki}\nu_{kj}]$ for $i \ne j$. The probability that two genes from $i$ and $j$ whose parents both lie in $k$ have the same parent is

$$p_{ijk} = \Bigl(1 - \frac{1}{2Nu_i}\Bigr)^{-\mathbf{1}\{i=j\}} \frac{V_{kij}\,u_k}{2N u_i u_j Q_{ij,kk}},$$

and the recursion holds with

$$A_{ij,kl} = \Bigl(1 - \frac{1}{2Nu_i}\Bigr)^{\mathbf{1}\{i=j\}} \Bigl(\frac{1 - p_{ijk}}{1 - 1/(2Nu_k)}\Bigr)^{\mathbf{1}\{k=l\}} Q_{ij,kl}.$$

3. (Large populations.) Let $N \to \infty$ with $u$ and the migration matrices fixed and the assumptions of the Setting holding for each $N$; put $\epsilon = 1/(2N^\beta)$ for a fixed $0 < \beta \le 1$, and let $A = A(\epsilon)$ and $Q = Q(\epsilon)$ be the matrices of item 2. Assume that
   - $Q(\epsilon) = Q(0) + \dot Q\,\epsilon + o(\epsilon)$ as $\epsilon \to 0$;
   - $Q(0)$ is the transition matrix of a Markov chain (not necessarily irreducible) with a unique equilibrium distribution $\rho(0) = (\rho_{ij}(0))$, the left eigenvector of its unique largest eigenvalue $1$;
   - the limits $\sigma_{ijk} = \lim_{N \to \infty} V_{kij}\,u_k^2 / \bigl((Nu_k)^{1-\beta} u_i u_j Q_{ij,kk}(0)\bigr)$ exist for all $i, j, k$;
   - the largest eigenvalue $\lambda(\epsilon)$ of $A(\epsilon)$ and its left eigenvector $\rho(\epsilon)$ are differentiable at $\epsilon = 0$.

   Then

$$N_{eE} = \frac{N^\beta}{C} + o(N^\beta), \qquad C = \sum_{i,j,k} \rho_{ij}(0)\,\sigma_{ijk}\,\frac{Q_{ij,kk}(0)}{u_k^\beta},$$

The constant $C$ can be read as the equilibrium coalescence rate of two lineages when time is counted in units of $2N^\beta$ generations. On this ground the source expects $N_{eE}$ to be asymptotically equivalent to the coalescence effective size whenever the latter exists, and checks $N_{eC} = N^\beta / C$ in its examples; it does not prove this in general.

## Expansion

A combination of predicted gene diversities with positive weights is the expectation of a quadratic function of $X_t$ that vanishes exactly at fixation, so by the decay statement above, which rests on the Perron–Frobenius decomposition of $P$, it decays at rate $\lambda_3(P)$; matching this with the decay $A^t \approx \lambda_{\max}(A)^t r\rho$ of the linear recursion identifies the two eigenvalues. Tracing two lineages back one generation, they either coalesce (contributing zero diversity) or move to a pair of parental subpopulations $(k,l)$ with probability $Q_{ij,kl}$, which yields the recursion. In the large-population limit $A(\epsilon) = A(0) + \epsilon \dot A + o(\epsilon)$ with $A(0) = Q(0)$ stochastic, and first-order eigenvalue perturbation gives $\lambda_{\max}(A(\epsilon)) = 1 + \dot\lambda\,\epsilon + o(\epsilon)$ with $\dot\lambda = \rho(0)\dot A\,\mathbf{1} < 0$, so $1 - \lambda_{\max}(A) \approx -\epsilon\,\rho(0)\dot A\,\mathbf{1}$, the averaged coalescence rate. Island models, strong and weak migration limits, and Ewens' 1982 results appear as special cases.

## Depends on

- [Inbreeding, variance and eigenvalue effective population sizes](../../../population-genetics/effective-population-size/effective-population-size-definitions.md)

## Proof depends on

- [Perron–Frobenius theorem for irreducible nonnegative matrices](../../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius.md)

## Sources

- O. Hössjer, "On the eigenvalue effective size of structured populations", Journal of Mathematical Biology (2015), Eqs (19)–(25), Theorem 1 and Corollary 1, Theorem 2 and Corollary 2 (Eq 32), Theorem 3 (Eqs 39–41), Theorems 4–5 (Eqs 68–83), <https://doi.org/10.1007/s00285-014-0832-5>, PMCID PMC4532751.
