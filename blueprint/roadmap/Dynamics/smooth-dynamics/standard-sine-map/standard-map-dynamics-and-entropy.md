# Standard map, vector growth, and metric entropy

For real $k$, let $F_k(x,y)=(x+y+k\sin(2\pi x),\ y+k\sin(2\pi x))$ on $(\mathbb R/\mathbb Z)^2$, with coordinates taken modulo $1$ and normalized area $m$.

For a measurable $P$ into a finite label set, write $p_w=m\{z:P(F_k^i z)=w_i\ (0\le i<n)\}$ for a word $w$ of length $n$. The partition rate is $\inf_{n\ge1}(-\sum_w p_w\log p_w)/n$, where zero masses contribute zero; the metric entropy $h_m(F_k)$ is the supremum over all such partitions. Rates are taken in the extended nonnegative reals (the source uses the nonnegative embedding of each normalized block entropy).

Use the Euclidean norm on $\mathbb R^2\simeq\mathbb C$ for vectors and its operator norm for matrices. Set $D_k(x)=\begin{pmatrix}1+a & 1\\ a & 1\end{pmatrix}$ with $a=2\pi k\cos(2\pi x)$, and let $A_n(z)=D_k((F_k^{n-1}z)_1)\cdots D_k(z_1)$ for $n\ge1$, with $A_0=I$. This is the source's transfer matrix conjugated by $(r,s)\mapsto(r,r-s)$. A positive spectrum at $z$ means there are $\ell>0$ and a nonzero $s\in\mathbb R^2$ for which $\lim_{n\to\infty}\log\|A_n(z)v\|/n$ is $-\ell$ for every nonzero $v$ on the line $\mathbb R s$ and $\ell$ for every other nonzero $v$. For the unused zero-exponent branch of the vector-spectrum predicate, require limit zero for every nonzero vector.

The finite-block infimum above defines the rate directly. By contrast, the general [Kolmogorov–Sinai entropy](../../ergodic-theory/kolmogorov-sinai-entropy/ks-entropy.md) uses a limsup for each partition. The two conventions agree for the area-preserving standard map by subadditivity of the block entropies. This comparison is not part of the map or vector-growth definition; the Bernoulli component uses neither entropy convention.

## Expansion

Verify the torus lift and its derivative matrix, compare normalized product area with Haar probability, and identify the finite-word infimum on this measure-preserving map with the finite-partition entropy rate. Keep operator-norm growth out of the vector-spectrum predicate; it is a separate condition in the combined tail result.

## Sources

- OpenAI, [Comparator statement and definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/StandardMapLyapunov.lean#L10-L93) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/146.md).
- OpenAI, [Comparator statement and definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/StandardMapEntropy.lean#L10-L43).
