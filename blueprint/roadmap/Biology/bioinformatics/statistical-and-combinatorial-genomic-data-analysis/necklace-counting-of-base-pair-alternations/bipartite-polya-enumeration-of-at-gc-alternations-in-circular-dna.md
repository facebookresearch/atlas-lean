# Bipartite Pólya enumeration of AT/GC alternations in circular DNA

**Setting.** A circular (periodic) double-stranded DNA chain of $N_{AT}$ adenine–thymine and $N_{GC}$ guanine–cytosine base pairs has an even number $\alpha = 2M$ of **alternations** (positions where an AT pair is followed by a GC pair or vice versa); equivalently it consists of $M$ AT-blocks and $M$ GC-blocks, alternating around the circle, each of length at least one. Configurations equal up to rotation and reflection of the circle are identified, so one counts orbits of the dihedral group $D_M$ acting on the $2M$ blocks.

**Definitions.** A group action of a finite group $G$ on $A = X \sqcup Y$ is **partition-preserving** if $gx \in X \iff x \in X$. Its **bipartite cycle index** is

$$\tilde Z_G(x_1,\dots,x_n, y_1,\dots,y_n) = \frac1{|G|}\sum_{g\in G}\prod_k x_k^{C^X_k(g)}\,y_k^{C^Y_k(g)},$$

where $C^X_k(g)$ and $C^Y_k(g)$ count the $k$-cycles of $g$ inside $X$ and inside $Y$.

**Theorem (bipartite Pólya enumeration).** Let colours $\Omega = \Omega_X \sqcup \Omega_Y$ carry weights with generating functions $f_X, f_Y$, and let valid colourings assign $\Omega_X$-colours to $X$ and $\Omega_Y$-colours to $Y$. Then the bivariate generating function, by total weight in $\Omega_X$ and in $\Omega_Y$, of the number of orbits of valid colourings is

$$\mathrm{Orbits}(x,y) = \tilde Z_G\big(f_X(x), f_X(x^2), \dots;\ f_Y(y), f_Y(y^2), \dots\big).$$

**Application.** Colouring each block by its length gives $f(x) = x + x^2 + \dots = x/(1-x)$. With Euler's totient $\varphi$, for $M$ odd

$$\mathrm{Orbits}(x,y) = \frac1{2M}\sum_{d\mid M}\varphi(d)f(x^d)^{M/d}f(y^d)^{M/d} + \frac12 f(x)f(y)f(x^2)^{\frac{M-1}2}f(y^2)^{\frac{M-1}2},$$

and for $M$ even the reflection term is replaced by $\frac14 f(x)^2f(x^2)^{\frac{M-2}2}f(y^2)^{\frac M2} + \frac14 f(y)^2f(y^2)^{\frac{M-2}2}f(x^2)^{\frac M2}$. The number of distinct circular chains with $2M$ alternations is the coefficient of $x^{N_{AT}}y^{N_{GC}}$, computable in closed form from

$$[x^r]f(x^a)^b = \begin{cases} 1, & b = r = 0,\\ \binom{r/a - 1}{b - 1}, & b \ge 1,\ a \mid r,\ r \ge ab,\\ 0, & \text{otherwise}\end{cases}$$

(the case $b = 0$ occurs in the reflection terms for $M = 1, 2$); normalizing over $M$ gives the probability distribution of the number of alternations, a measure of sequence heterogeneity relevant to DNA breathing dynamics.

## Depends on

- [Euler's totient function](../../../../NumberTheory/arithmetic-functions/divisor-totient-functions/euler-totient.md)

## Proof sketch

The proof follows Burnside's lemma: an element $g$ fixes a valid colouring exactly when the colouring is constant on each cycle of $g$, and since cycles do not mix $X$ and $Y$, a $k$-cycle in $X$ contributes $f_X(x^k)$ and a $k$-cycle in $Y$ contributes $f_Y(y^k)$; averaging over $G$ gives the cycle index. For the dihedral action on alternating blocks, rotations by multiples of $2$ preserve the block types (giving the totient sum), and reflections pair blocks either across vertices or across edges, which is why the parity of $M$ matters. The coefficient formula expands $f(x^a)^b = x^{ab}(1 - x^a)^{-b} = \sum_{j\ge0}\binom{j+b-1}{b-1}x^{a(b+j)}$ for $b \ge 1$, while $f(x^a)^0 = 1$.

## Sources

- Malcolm Hillebrand, Guy Paterson-Jones, George Kalosakas and Charalampos Skokos, "Distribution of Base Pair Alternations in a Periodic DNA Chain: Application of Pólya Counting to a Physical System", *Regular and Chaotic Dynamics* 23 (2018), 135–151, <https://doi.org/10.1134/s1560354718020016>. Preprint version: arXiv:1805.06245 (2018), Section 2 (bipartite cycle index, bipartite Pólya enumeration theorem and corollary, coefficient lemmas) and Section 3 (algorithm), <https://doi.org/10.48550/arXiv.1805.06245>.
