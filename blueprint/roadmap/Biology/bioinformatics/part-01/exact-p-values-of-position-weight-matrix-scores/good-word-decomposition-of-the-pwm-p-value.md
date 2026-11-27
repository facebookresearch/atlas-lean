# Good-word decomposition of the PWM p-value

**Setting.** Let $M$ be a real position weight matrix of length $m$ over a finite alphabet $\Sigma$, and let letters be drawn i.i.d. from a background distribution $p$ on $\Sigma$. For a slice $M[i..j]$ put

$$\mathrm{BS}(M[i..j])=\sum_{k=i}^{j}\max_{x\in\Sigma} M(k,x),\qquad \mathrm{WS}(M[i..j])=\sum_{k=i}^{j}\min_{x\in\Sigma} M(k,x),$$

with empty slices scoring $0$. Let $Q(M[1..i],s)$ be the probability that a random word of length $i$ has score $s$ under $M[1..i]$, and $\mathrm{P\text{-}value}(M,\alpha)=\Pr[\mathrm{Score}(u,M)\ge\alpha]$.

**Good words (Definition 2).** A word $u=u_1\cdots u_i$ is good for $\alpha$ if
1. $\mathrm{Score}(u,M[1..i])\ge \alpha-\mathrm{WS}(M[i+1..m])$, and
2. $\mathrm{Score}(u_1\cdots u_{i-1},M[1..i-1])<\alpha-\mathrm{WS}(M[i..m])$.

**Lemmas 3–5.**
- Every extension of a good word to length $m$ scores at least $\alpha$.
- Every word of length $m$ scoring at least $\alpha$ has exactly one good prefix.
- Hence

$$\mathrm{P\text{-}value}(M,\alpha)=\sum_{\substack{1\le i\le m,\ x\in\Sigma,\ s<\alpha-\mathrm{WS}(M[i..m])\\ s+M(i,x)\ge\alpha-\mathrm{WS}(M[i+1..m])}} Q(M[1..i-1],s)\,p(x).$$

**Useful scores (Lemma 2).** To obtain the distribution on a score range $[\alpha,\beta]$, the only prefix values needed are $Q(M[1..i],s)$ with $\alpha-\mathrm{BS}(M[i+1..m])\le s\le\beta-\mathrm{WS}(M[i+1..m])$.

**Column order (Lemmas 6–7).** Permuting the columns of $M$ leaves the score distribution unchanged, and ordering columns so that $\delta_i=\mathrm{BS}(M[i..i])-\mathrm{WS}(M[i..i])$ is non-increasing minimizes the total size of the score ranges visited.

## Depends on

- [Score of a site under a position weight matrix](../../position-weight-matrices/score.md)
- [Background score distribution of an integer matrix](../../position-weight-matrices/score-dist.md)

## Expansion

Since every column score is at least its minimum, $\mathrm{Score}(uw,M)\ge \mathrm{Score}(u,M[1..i])+\mathrm{WS}(M[i+1..m])$, which gives the first lemma. Condition 1 is inherited by longer prefixes because $M(i+1,x)\ge \mathrm{WS}(M[i+1..m])-\mathrm{WS}(M[i+2..m])$, so the good prefix is the shortest prefix meeting condition 1, and it is unique. The words scoring at least $\alpha$ are therefore partitioned by their good prefixes, and the probability of the block with good prefix ending in letter $x$ at position $i$ is $Q(M[1..i-1],s)p(x)$. The dynamic program therefore stops extending a prefix as soon as it becomes good, and prefix scores at or above $\alpha-\mathrm{WS}(M[i..m])$ never need to be stored.

## Sources

- H. Touzet and J.-S. Varré, "Efficient and accurate P-value computation for Position Weight Matrices", Algorithms for Molecular Biology 2 (2007) 15. <https://doi.org/10.1186/1748-7188-2-15>, PMCID PMC2238751. Definitions 1–2, Lemmas 2–7.
