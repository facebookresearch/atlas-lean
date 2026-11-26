# Adjacency sandwich bounds for breakpoint medians of permutations

**Setting.** A linear unichromosomal genome on $n$ unsigned genes is a permutation $\pi=\pi_1\cdots\pi_n\in S_n$ with adjacency set $\mathcal{A}_\pi=\{\{\pi_i,\pi_{i+1}\}:1\le i\le n-1\}$. The breakpoint distance is $d(x,y)=n-1-|\mathcal{A}_x\cap\mathcal{A}_y|=\tfrac12|\mathcal{A}_x\triangle\mathcal{A}_y|$. For $X=\{x_1,\dots,x_k\}\subset S_n$ the total distance of $m$ is $d_T(m,X)=\sum_i d(m,x_i)$, a **breakpoint median** is a minimizer, $M(X)$ is the set of medians and $\mu(X)$ the minimum. For $U\subseteq X$ let $\mathcal{B}^X_U$ be the adjacencies present in every genome of $U$ and in no genome of $X\setminus U$, and $\mathcal{A}_{ij}=\mathcal{A}_{x_i}\cap\mathcal{A}_{x_j}$.

**Theorem.**
1. *(Two genomes.)* For $x,y,z\in S_n$, $z\in M(\{x,y\})$ iff $\mathcal{A}_{x,y}\subseteq\mathcal{A}_z\subseteq\mathcal{A}_x\cup\mathcal{A}_y$.
2. *(Sandwich.)* If $m\in S_n$ satisfies

$$\bigcup_{i<j}\mathcal{A}_{x_ix_j}\ \subseteq\ \mathcal{A}_m\ \subseteq\ \bigcup_{x\in X}\mathcal{A}_x,$$

then $m\in M(X)$ and

$$\mu(X)=(k-1)(n-1)-\sum_{r=1}^k(r-1)\sum_{|U|=r}|\mathcal{B}^X_U| .$$

3. *(Bounds.)* For every $X$, with $\lambda_n(X)=\sum_{r}(r-1)\sum_{|U|=r}|\mathcal{B}^X_U|$ and $\upsilon_n(X)=\max_i\sum_{j\ne i}|\mathcal{A}_{ij}|$,

$$(k-1)(n-1)-\lambda_n(X)\ \le\ \mu(X)\ \le\ (k-1)(n-1)-\upsilon_n(X).$$

4. *(Tree search spaces.)* The rooted labeled trees built by extending prefixes only through adjacencies allowed by local constraints derived from $X$ are connected, contain $X$ among their leaves, contain every breakpoint median, and every leaf genome $y$ satisfies $0\le d_T(y,X)-\mu(X)\le\lambda_n(X)$.

## Expansion

Each adjacency of $m$ contributes to $d_T(m,X)$ through the number of inputs that share it: an adjacency in $\mathcal{B}^X_U$ saves $|U|$ units, and since $m$ has exactly $n-1$ adjacencies, the best conceivable total is reached by containing every adjacency shared by at least two inputs and using no adjacency absent from all inputs. That gives the sandwich formula and, in general, the lower bound; choosing $m=x_i$ itself gives the upper bound. The breakpoint median problem is NP-hard already for three unichromosomal genomes and medians are far from unique, so the tree algorithms prune the $n!$ search space to permutations compatible with the local adjacency constraints while provably keeping all medians.

## Sources

- Poly H. da Silva, Arash Jamshidpey and David Sankoff, "Tree-based Algorithms for Breakpoint Median and Near-Median Genomes", arXiv:2610.40667 (2026), Section 2 (definitions), Theorems 1–3 and 7, <https://doi.org/10.48550/arXiv.2610.40667>.
