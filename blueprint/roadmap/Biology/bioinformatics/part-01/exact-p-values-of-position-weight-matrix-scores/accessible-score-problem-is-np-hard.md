# The accessible score problem is NP-hard

**Setting.** Let $\Sigma$ be a finite alphabet and $M$ an integer position weight matrix of length $m$, with entries $M(i,x)\in\mathbb{Z}$ for $1\le i\le m$, $x\in\Sigma$. The score of a word $u=u_1\cdots u_m\in\Sigma^m$ is $\mathrm{Score}(u,M)=\sum_{i=1}^m M(i,u_i)$. An integer $t$ is *accessible* for $M$ if $\mathrm{Score}(u,M)=t$ for some $u\in\Sigma^m$.

**Problem (ACCESSIBLE SCORE).** Given $M$ and an integer $t$, decide whether $t$ is accessible.

**Theorem 1.** ACCESSIBLE SCORE is NP-hard, already over a two-letter alphabet.

Hence, unless P = NP, neither the score-to-P-value problem (when every word has positive probability) nor the P-value-to-threshold problem (under a uniform background) has a polynomial-time algorithm. The known dynamic programmes take time proportional to $m$ times the number of attainable scores, which can be as large as $|\Sigma|^m$.

## Depends on

- [Score of a site under a position weight matrix](../../position-weight-matrices/score.md)

## Expansion

Lemma 1 of the source gives a polynomial reduction from SUBSET SUM. For positive integers $A=\{a_0,\dots,a_n\}$ and target $s$, take $\Sigma=\{x,y\}$, length $n+1$, and $M(i,x)=a_i$, $M(i,y)=0$. Subsets $A'\subseteq A$ correspond bijectively to words $u\in\Sigma^{n+1}$ (put $x$ at position $i$ exactly when $a_i\in A'$), and $\mathrm{Score}(u,M)=\sum_{a\in A'}a$. So $s$ is accessible exactly when some subset sums to $s$. Because SUBSET SUM is NP-complete but pseudo-polynomial, dynamic programming over accessible scores remains the practical route.

## Sources

- H. Touzet and J.-S. Varré, "Efficient and accurate P-value computation for Position Weight Matrices", Algorithms for Molecular Biology 2 (2007) 15. <https://doi.org/10.1186/1748-7188-2-15>, PMCID PMC2238751. Theorem 1 and Lemma 1.
