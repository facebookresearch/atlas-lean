# Return locations and size of the largest irreducible substructure

**Setting.** Represent an RNA structure on $[n]$ as a diagram: non-crossing or crossing arcs $(i,j)$ with $i<j$ drawn above the backbone, each vertex in at most one arc. A structure is **$k$-noncrossing** if no $k$ arcs mutually cross ($k=2$ gives secondary structures, $k\ge3$ allows pseudoknots). It is **$\sigma$-canonical** if every stack of nested parallel arcs has length $\ge\sigma$, and every arc has length $j-i\ge4$. A *gap* is a maximal run of isolated vertices not covered by any arc. A (sub)structure is **irreducible** if it cannot be decomposed into a nontrivial sequence of gaps and substructures. Every structure decomposes uniquely into an alternating sequence of gaps and irreducible substructures. Position $i$ is a **return** of $s$, written $i\in\chi(s)$, if $i$ is the right endpoint of an irreducible substructure.

Let $\mathbf T_{k,\sigma}(z)=\sum_n T_{k,\sigma}(n)z^n$ count such structures, let $\alpha_{k,\sigma}$ be its unique real positive dominant singularity, and set $\mu=(k-1)^2+\frac{k-1}{2}$. Then $T_{k,\sigma}(n)\sim c\,n^{-\mu}\alpha_{k,\sigma}^{-n}$. Structures are drawn uniformly at random among those of length $n$.

**Theorem.** Let $k\ge2$ and $\sigma\ge1$.

1. *(Returns.)* As $n\to\infty$,

$$\mathbb P[i\in\chi(s)]\sim\Big(1-\frac in\Big)^{-\mu}\big[i^{-\mu}-(i-1)^{-\mu}\alpha_{k,\sigma}\big],$$

and for $i\to\infty$ and $n-i\to\infty$,

$$\frac{\mathbb P[i+1\in\chi(s)]}{\mathbb P[i\in\chi(s)]}\sim\Big(\frac{n-i}{n-i-1}\Big)^{\mu}.$$

Returns therefore concentrate at the $3'$ end of the sequence, with a polynomial blow-up of exponent $\mu$.
2. *(Unique irreducible component.)* If a structure has a unique irreducible substructure $s$, then

$$\mathbb P\big(|s|=x_n\mid s\text{ unique}\big)\sim\frac{(n-x_n+1)\,x_n^{-\mu}\alpha_{k,\sigma}^{-x_n}}{(1-\alpha_{k,\sigma})^{-2}\,n^{-\mu}\alpha_{k,\sigma}^{-n}},$$

so $|s|\ge n-O(1)$.
3. *(Two irreducible components.)* If a structure has exactly two irreducible substructures $s_1,s_2$ with $x_n=|s_1|\ge|s_2|$, then $\mathbb P(|s_1|=x_n)=o(1)$ when $n-x_n\to\infty$. When $n-x_n\to a<\infty$ the probability is asymptotic to $2(1-\alpha_{k,\sigma})^3c_a\alpha_{k,\sigma}^{a}$ for constants $c_a>0$. Hence the largest component again has size $n-O(1)$ almost surely.
4. *(Stack-length rescaling.)* The irreducible counts $R_{k,\sigma}(n)$ satisfy

$$R_{k,\sigma}(n)\sim\Big(\frac{\ln\alpha_{k,\sigma}}{\ln\alpha_{k,\sigma+1}}\Big)^{-\mu}R_{k,\sigma+1}\Big(\Big[\frac{\ln\alpha_{k,\sigma}}{\ln\alpha_{k,\sigma+1}}\Big]n\Big),$$

so increasing the minimum stack size acts asymptotically as a linear rescaling of length.

Combined with the discrete-gamma law for the number of irreducible components, a typical long $k$-noncrossing structure has one or two irreducible blocks, and the largest has size $n-O(1)$. This large block is the main factor in the folding time of minimum free energy configurations.

## Expansion

For a return at $i$, the structure splits into an arbitrary structure on $[1,j]$, an irreducible one on $[j+1,i]$ and an arbitrary one on $[i+1,n]$. Hence $a_i(n)=\sum_j T(j)R(i-j)T(n-i)$. Dividing by $T(n)\sim c\,n^{-\mu}\alpha^{-n}$ and using the singular expansions of $\mathbf T$ and $\mathbf R=1-z-1/\mathbf T$, the exponential factors cancel, and the polynomial factors give the $(1-i/n)^{-\mu}$ profile. For a unique component of size $x_n$ there are $n-x_n+1$ placements, each contributing $R(x_n)\approx c\,x_n^{-\mu}\alpha^{-x_n}$. Relative to $T(n)$ this decays like $\alpha^{n-x_n}$, which forces $n-x_n=O(1)$. The same counting with two blocks, together with the symmetry factor $2$, gives item 3.

Item 1 is Proposition 2 (Section 4), items 2–3 are Lemmas 2–3 (Section 5), and item 4 is Proposition 1 (Section 3) of the source.

## Sources

- E. Y. Jin, C. M. Reidys, "Irreducibility in RNA structures", arXiv:0902.3784 (2009). <https://doi.org/10.48550/arXiv.0902.3784>
