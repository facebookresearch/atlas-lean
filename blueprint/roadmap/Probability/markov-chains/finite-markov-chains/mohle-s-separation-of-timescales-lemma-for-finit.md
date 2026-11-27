# Möhle's lemma on Markov chains with two time scales

Let $\Pi_N$, $N\ge1$, be stochastic matrices on a finite set with

$$\Pi_N=A+N^{-1}B+o(N^{-1}) \qquad (N\to\infty),$$

where $A$ is stochastic and $P=\lim_{k\to\infty}A^k$ exists. Put $G=PBP$. Then for every $t>0$,

$$\lim_{N\to\infty}\Pi_N^{\lfloor Nt\rfloor}=P e^{tG}=P-I+e^{tG}.$$

The last two expressions agree because $P^2=P$ and $PG=GP=G$. At $t=0$ the left side is $I$, so the displayed identity at zero holds only if $P=I$.

## Proof depends on

- [Jordan normal form](../../../LinearAlgebra/eigenvalues-and-canonical-forms/jordan-normal-form/exists-jordan-normal-form-of-splits.md): used after complexification to bound the powers of the transient matrix.

## Expansion

Here is a direct finite-dimensional proof, including the stated small-error term. The empty state space is trivial; otherwise use the maximum absolute row-sum norm. Stochastic matrices and their powers have norm $1$. Taking limits gives $AP=PA=P=P^2$. For $R=A-P$ one has $R^a=A^a-P$ for $a\ge1$, so $R^a\to0$. Its powers decay geometrically: after complexification, every eigenvalue has modulus less than $1$, since an eigenvector otherwise contradicts $R^a\to0$. Powers of a Jordan block with nonzero eigenvalue are polynomial factors times decaying geometric terms, and nilpotent blocks vanish after finitely many powers. Thus $\|R^a\|\le c\theta^a$ for some $c<\infty$ and $0<\theta<1$. In particular

$$S:=\sum_{a=0}^{\infty}\|A^a-P\|<\infty,$$

where the $a=0$ summand is $\|I-P\|$.

Put $C_N=\Pi_N-A$. Then $NC_N\to B$ and, for all sufficiently large $N$, $\|C_N\|\le\kappa/N$ for a fixed $\kappa$. For $m=\lfloor Nt\rfloor$, expand by the number $j$ of factors $C_N$:

$$\Pi_N^m=\sum_{j=0}^{m} W_{N,j},\qquad
W_{N,j}=\sum_{\substack{a_0,\dots,a_j\ge0\\a_0+\dots+a_j=m-j}}
 A^{a_0}C_NA^{a_1}\cdots C_NA^{a_j}.$$

There are $\binom mj$ such words. Replace every $A^{a_i}$ by $P$. Their sum becomes

$$V_{N,j}=\binom mj P(C_NP)^j.$$

For a fixed $j\ge1$, telescope the difference between each original product and its all-$P$ product. Every other $A^{a_i}$ and $P$ has norm at most $1$. Summing the distinguished exponent against $S$, and counting compositions of the remaining exponents, gives, once $m\ge j$,

$$\|W_{N,j}-V_{N,j}\|
 \le (j+1)S\binom{m-1}{j-1}\|C_N\|^j \longrightarrow0.$$

Indeed, with one exponent fixed to $a$, the number of choices of the other $j$ exponents is $\binom{m-a-1}{j-1}\le\binom{m-1}{j-1}$; the bound is $O(m^{j-1}N^{-j})$ for fixed $j$. Also $W_{N,0}=A^m\to P$. For fixed $j\ge1$,

$$V_{N,j}\longrightarrow \frac{t^jG^j}{j!},$$

since $NP C_NP\to G$, $\binom mj/N^j\to t^j/j!$, and $P(C_NP)^j=(PC_NP)^j$ for $j\ge1$.

To justify summing these limits, set $W_{N,j}=0$ when $j>m$. Independently of the preceding fixed-$j$ error bound,

$$\|W_{N,j}\|\le\binom mj\|C_N\|^j\le\frac{(\kappa t)^j}{j!}.$$

This is summable over $j$, so dominated convergence for the series gives

$$\Pi_N^{\lfloor Nt\rfloor}\longrightarrow P+\sum_{j\ge1}\frac{t^jG^j}{j!}=P-I+e^{tG}.$$

Thus the argument covers $o(N^{-1})$, not only $O(N^{-2})$.

For an explicit two-state example, take

$$A=\begin{bmatrix}1&0\\1/2&1/2\end{bmatrix},\quad
 B=\begin{bmatrix}-1&1\\0&0\end{bmatrix},\quad
 \Pi_N=A+B/N.$$

These are stochastic for $N\ge1$, $P=\begin{bmatrix}1&0\\1&0\end{bmatrix}$, and $PBP=0$. The stationary row of $\Pi_N$ is $(N/(N+2),2/(N+2))$, and its other eigenvalue is $1/2-1/N$. Hence $\Pi_N^{\lfloor Nt\rfloor}\to P$ for $t>0$, while its zeroth power is $I$. For $A=I$ the lemma reduces to the compound-interest limit with the stated vanishing perturbation.

## Background

- [Compound-interest limit in a Banach algebra](../../../Analysis/operator-algebras/exponential-limits-and-the-lie-trotter-formula/tendsto-one-add-inv-smul-pow.md): the special case $A=P=I$.

## Sources

- M. Möhle, "A convergence theorem for Markov chains arising in population genetics and the coalescent with selfing", Advances in Applied Probability 30 (1998), 493–512, Lemma 1.
- I. Kaj, S. M. Krone and M. Lascoux, "Coalescent theory for seed bank models", Journal of Applied Probability 38 (2001), 285–300, <https://doi.org/10.1239/jap/996986745>; author preprint dated 22 September 2000, Section 3, equations (10)–(11), which apply the $O(N^{-2})$ form with $P=\lim_k A^k$ and $G=PBP$. The proof above establishes the stated general error term directly.
