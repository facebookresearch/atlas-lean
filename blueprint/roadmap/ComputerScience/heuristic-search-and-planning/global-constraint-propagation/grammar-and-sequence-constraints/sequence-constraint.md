# AMONG and SEQUENCE constraints

AMONG bounds how many variables of a sequence take a value from a given set; SEQUENCE imposes the same AMONG bounds on every window of $k$ consecutive variables, as in rostering rules such as "at least 2 days off in every 7".

Let $X_1,\dots,X_n$ be distinct variables with finite domains and $v$ a set of values.

- $\mathrm{AMONG}(l,u,[X_1,\dots,X_k],v)$, for integers $0\le l\le u\le k$, allows exactly the assignments with $l\le|\{i: X_i\in v\}|\le u$.
- $\mathrm{SEQUENCE}(l,u,k,[X_1,\dots,X_n],v)$, for $1\le k\le n$ and $0\le l\le u\le k$, allows exactly the assignments satisfying $\mathrm{AMONG}(l,u,[X_i,\dots,X_{i+k-1}],v)$ for every $1\le i\le n-k+1$. Each $X_i,\dots,X_{i+k-1}$ is a **window**. With $l=0$ it is called AtMostSeq.
- The generalized form imposes $\mathrm{AMONG}(l_j,u_j,s_j,v)$ on arbitrary given subsequences $s_j$ with their own bounds.

Channelling each $X_i$ to a 0/1 variable $Y_i$ by the binary constraint $Y_i=1\iff X_i\in v$ does not weaken [generalized arc consistency](../generalized-arc-consistency.md) of a single SEQUENCE (or AMONG) constraint posted on $Y_1,\dots,Y_n$: Maher, Narodytska, Quimper and Walsh note that the constraint graph of this encoding, one global constraint together with the $n$ channelling constraints, is Berge-acyclic. So one may assume $X_i\in\{0,1\}$ and $v=\{1\}$, and then SEQUENCE reads $l\le X_i+\dots+X_{i+k-1}\le u$ for every window.

## Depends on

- [Generalized arc consistency](../generalized-arc-consistency.md): the consistency preserved by the channelling.

## Proof depends on

None.

## Expansion

Support lifting for the channelling: suppose every constraint of the encoding is GAC and $x\in D(X_i)$. The channelling constraint gives $y_i=[x\in v]\in D(Y_i)$, the 0/1 constraint gives a support $(y_1,\dots,y_n)$ with that $y_i$, and choosing $x$ for $X_i$ and, for $j\ne i$, a value of $D(X_j)$ inside $v$ when $y_j=1$ and outside $v$ when $y_j=0$ (it exists because $y_j$ is supported by its channelling constraint) gives a support of $X_i=x$ for the original constraint.

Decomposing SEQUENCE into its AMONG constraints hinders propagation in general, because neighbouring windows overlap in $k-1$ variables and GAC on each window does not imply GAC on the conjunction. For AtMostSeq ($l=0$) the decomposition does achieve GAC: AtMost is monotone (any support stays a support when 1s are replaced by 0s), so a support for $X=w$ is obtained by giving every other variable the value 0 where allowed, a fact due to Bessiere et al. (the SLIDE paper) and recalled by the source. Bergman, Cire and van Hoeve use the same definitions (their Definitions 1–3, with window length $q$; they also allow $q=0$, excluded here) for MDD propagation. Propagation reports failure when some domain becomes empty.

## Sources

- M. J. Maher, N. Narodytska, C.-G. Quimper and T. Walsh, "Flow-based propagators for the SEQUENCE and related global constraints", *Principles and Practice of Constraint Programming – CP 2008*, Lecture Notes in Computer Science 5202 (2008), 159–174, doi:10.1007/978-3-540-85958-1_11. Definitions of AMONG, SEQUENCE and windows, channelling to 0/1 variables and the remarks on decomposition, §3 of arXiv:0909.4452v1, [https://arxiv.org/abs/0909.4452v1](https://arxiv.org/abs/0909.4452v1).
- D. Bergman, A. A. Cire and W.-J. van Hoeve, "MDD propagation for sequence constraints", *Journal of Artificial Intelligence Research* 50 (2014), 697–722, doi:10.1613/jair.4199. Definitions 1–3 (Among, Sequence, Gen-Sequence), §2.
