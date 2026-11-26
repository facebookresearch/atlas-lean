# Genetic weight of a beneficial mutant in a biparental Moran model

**Model.** A population of fixed size $N$, individuals $I_N=\{1,\dots,N\}$, each advantaged or disadvantaged at a selected locus; initially only individual 1 is advantaged. At each step two parents $\mu_n,\pi_n$ are drawn independently and uniformly from $I_N$, and an individual $\kappa_n$ drawn uniformly from the **disadvantaged** class (infinite viability selection) is replaced by their child, which inherits the mother's type; once all are advantaged the model is neutral. Genetic inheritance at an unlinked neutral locus is tracked by stochastic matrices $A_0=I$,
$$A_{n+1}(i,j)=\begin{cases}A_n(i,j), & i\ne\kappa_n,\\ \tfrac12\big(A_n(\mu_n,j)+A_n(\pi_n,j)\big), & i=\kappa_n,\end{cases}$$
so $A_n(i,j)$ is the probability that a gene sampled from $i$ at time $n$ descends from $j$ at time 0. Split the total weight of the mutant ancestor by type: $B_n=\sum_{i\text{ advantaged}}A_n(i,1)$ and $C_n=\sum_{i\text{ disadvantaged}}A_n(i,1)$. Let $S_k$ be the first time there are $k$ advantaged individuals (so $S_N$ is fixation), and $k_N(y)=1\vee\lfloor yN\rfloor$.

**Theorem.** As $N\to\infty$, in $D([0,1],\mathbb R^2)$ with the Skorokhod $J_1$ topology,
$$\left(\frac1{\sqrt N}\binom{B_{S_{k_N(y)}}}{C_{S_{k_N(y)}}}\right)_{0\le y\le1}\Longrightarrow\left(W\binom{b(y)}{c(y)}\right)_{0\le y\le1},\qquad b(y)=\tfrac{2}{\sqrt\pi}\sqrt y\,(1+y),\quad c(y)=\tfrac{2}{\sqrt\pi}\sqrt y\,(1-y),$$
where $W>0$ a.s. is the unique $L^2$ solution with mean 1 of the smoothing equation
$$W\stackrel d=\sqrt U\,W^{(1)}+\tfrac12\sqrt{1-U}\,W^{(2)},\qquad U\sim\mathrm{Unif}[0,1],$$
with $W^{(1)},W^{(2)}$ independent copies of $W$ independent of $U$. In particular, at fixation $B_{S_N}/\sqrt N\Rightarrow\frac4{\sqrt\pi}W$ and $\mathbb E[B_{S_N}]/\sqrt N\to4/\sqrt\pi$: the mutant's genome makes up a vanishing fraction of order $N^{-1/2}$ of the population genome although its allele fixes.

## Expansion

Advantaged numbers grow as a pure-birth chain: from $k$ advantaged the next increase takes a geometric number of steps with success probability $k/N$. In the embedded chain the pair (imbalance between mean weight in the two classes, mean weight in the disadvantaged class) has a triangular drift matrix, and normalizing by explicit constants $a_{k,N}\asymp\sqrt k$ produces a martingale $M^{(N)}_k$ measuring the imbalance. Early on ($k\ll N$) paternal contributions are negligible and the maternal line of the mutant is a random recursive tree whose weight martingale converges to $M^\star_\infty$, characterized by the smoothing equation (a uniform split point of the tree, one subtree inheriting weight one half); this seeds $B_{k_0}/\sqrt{k_0}\Rightarrow\frac2{\sqrt\pi}M^\star_\infty$. In the macroscopic phase the martingale is asymptotically constant (its quadratic variation vanishes away from the origin), so $B$ and $C$ follow deterministic profiles scaled by the seeded random amplitude; boundary windows near $y=0$ and $y=1$ are controlled separately. Randomness is thus created only while the mutant lineage is microscopic.

## Sources

- C. Coron, O. Hénard, "Genetic weight of a mutant in a biparental Moran model with infinite selection", arXiv:2610.41650 (2026), Section 2 (model, Theorem 1 and the remark at fixation), Propositions 1-9, Lemmas 1-11, <https://doi.org/10.48550/arXiv.2610.41650>.
