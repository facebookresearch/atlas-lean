# Activities and average sensitivity of Boolean nested canalizing functions

**Setting.** A Boolean function $f:\mathbb{F}_2^n \to \mathbb{F}_2$, $n \ge 2$, is *nested canalizing* (NCF) iff it can be written uniquely in layer form

$$f = M_1\Big(M_2\big(\cdots(M_{r-1}(M_r \oplus 1)\oplus 1)\cdots\big)\oplus 1\Big)\oplus b,\qquad M_i = \prod_{j=1}^{k_i}(x_{i_j}\oplus a_{i_j}),$$

where the extended monomials $M_i$ use disjoint variable sets partitioning $\{1,\ldots,n\}$, $k_i \ge 1$ for $i<r$, $k_r \ge 2$, and $k_1 + \cdots + k_r = n$; $r$ is the number of layers. The *activity* of variable $x_i$ is $A_i^f = 2^{-n}\#\{x : f(x) \ne f(x \oplus e_i)\}$, and the *average sensitivity* is $s^f = \sum_i A_i^f$.

**Theorem (Hamming weight).** With $f_1 = M_1$ and $f_r = M_1(M_2(\cdots(M_r\oplus1)\cdots)\oplus1)$,

$$W(f_r) = \sum_{j=1}^{r}(-1)^{j-1}2^{\,n-\sum_{i=1}^{j}k_i},\qquad W(f_r\oplus 1) = \sum_{j=0}^{r}(-1)^j 2^{\,n-\sum_{i=1}^j k_i}.$$

**Theorem (activities and sensitivity).** Every variable in layer $l$ has the same activity

$$A^f_l = \frac{1}{2^{n-1}}\sum_{j=1}^{r-l+1}(-1)^{j-1}2^{\,n-\sum_{i=1}^{j+l-1}k_i},$$

and

$$s^f = \sum_{l=1}^r k_l A^f_l = \frac{1}{2^{n-1}}\sum_{l=1}^r k_l\sum_{j=1}^{r-l+1}(-1)^{j-1}2^{\,n-\sum_{i=1}^{j+l-1}k_i}.$$

**Corollary.** For $n \ge 3$, $A^f_1 > A^f_2 > \cdots > A^f_r$ (outer layers are strictly more influential), and

$$\frac{n}{2^{n-1}} \le s^f < 2 - \frac{1}{2^{n-2}} .$$

In particular every NCF has average sensitivity below $2$, independently of $n$. (This does not place NCFs in the ordered regime of the annealed approximation, whose threshold is average sensitivity $1$: for $n=3$ with layers of sizes $(1,2)$, $s^f=5/4$.)

## Expansion

Flipping a variable in layer $l$ changes $f$ only if all literals of layers $1,\ldots,l-1$ equal $1$ (otherwise an earlier layer canalizes) and the remaining literals of layer $l$ equal $1$; the probability of the latter event is $2^{-(k_1+\cdots+k_l-1)}$, and conditioned on it the flip changes the output exactly when the inner function $M_{l+1}(\cdots)\oplus1$ takes the value making the product sensitive, whose probability is computed from the Hamming-weight formula by inclusion–exclusion over deeper layers. The alternating sums decrease in $l$, giving the strict ordering. The lower bound $n/2^{n-1}$ is attained by a single layer ($r=1$, an extended monomial), while alternating layers of size one give $s^f\to4/3$ (Lemma 5.3(1) of the source), so they do not approach the upper bound.

## Sources

- Yuan Li, John O. Adeyeye, David Murrugarra, Boris Aguilar and Reinhard Laubenbacher, "Boolean nested canalizing functions: A comprehensive analysis", Theoretical Computer Science 481 (2013), 24–36, <https://doi.org/10.1016/j.tcs.2013.02.020>; numbering as in arXiv:1204.5203: Theorem 4.2 (layer form), Theorems 5.1 and 5.2 and Corollary 5.1.
