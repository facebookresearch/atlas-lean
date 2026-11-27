# Average-case depth hierarchy for constant-depth circuits

For $2\le d\le c\sqrt{\log n}/\log\log n$, an explicit read-once monotone depth-$d$ formula, the balanced Sipser function, agrees with every depth-$(d-1)$ circuit of size $2^{n^{1/(6(d-1))}}$ on at most a $1/2+n^{-\Omega(1/d)}$ fraction of inputs.

**Balanced Sipser function.** For an integer parameter $m$, $\mathsf{Sipser}_d$ is a read-once monotone formula in which every leaf is at depth $d$, every root-to-leaf path alternates between AND and OR gates, the gates adjacent to the inputs are AND gates (so the root is OR for even $d$ and AND for odd $d$), and all gates at the same depth $k$ have the same fan-in $w_k$: the bottom fan-in is $w_{d-1}=m$, the middle fan-ins are $w_k=\lfloor m2^m/\log e\rfloor$ for $1\le k\le d-2$, and the top fan-in $w_0$ is chosen so that the formula is essentially balanced under the uniform distribution. The number of variables is $n=\prod_{k=0}^{d-1}w_k$.

**Theorem.** There is an absolute constant $c>0$ such that for $2\le d\le c\sqrt{\log n}/\log\log n$, every circuit $C$ of depth at most $d-1$ and size at most $S=2^{n^{1/(6(d-1))}}$ over $\{0,1\}^n$ agrees with $\mathsf{Sipser}_d$ on at most

$$
\left(\tfrac12+n^{-\Omega(1/d)}\right)\cdot 2^n
$$

inputs. More strongly, the same bound holds for depth-$d$ circuits of size at most $S$ that either have bottom fan-in at most $\frac{\log n}{10(d-1)}$ or have the opposite alternation pattern to $\mathsf{Sipser}_d$ (top gate OR where $\mathsf{Sipser}_d$ has AND, and vice versa).

## Expansion

This is an average-case strengthening of the worst-case depth hierarchy of Sipser, Yao and Håstad, which separates depth $d$ from depth $d-1$ only for exact computation. The proof replaces random restrictions by *random projections*: variables are grouped into blocks $x_{a,1},\dots,x_{a,\ell}$, a restriction $\rho$ is applied, and every surviving variable of block $a$ is identified with one new variable $y_a$. A projection switching lemma, in the style of [Håstad's switching lemma](../../../../TheoryOfComputation/circuit-complexity/lower-bounds-for-ac0-circuits/hastad-s-switching-lemma.md), shows that the approximating circuit collapses under a carefully chosen adaptive sequence of random projections, while $\mathsf{Sipser}_d$ retains its structure. Because $\mathsf{Sipser}_d$ is monotone, its correlation with some variable or constant is at least $1/2+\Omega(1/n)$, so the correlation bound cannot be improved much for this function. Consequences in the source include that the polynomial hierarchy is infinite relative to a random oracle. Depth-$d$ Sipser functions (in Håstad's slightly different variant) also supply the [hard instances for tree-like bounded-depth Frege](tree-like-flattening-is-tight.md).

## Depends on

None.

## Proof depends on

- [Håstad's switching lemma](../../../../TheoryOfComputation/circuit-complexity/lower-bounds-for-ac0-circuits/hastad-s-switching-lemma.md)

## Sources

- Benjamin Rossman, Rocco A. Servedio and Li-Yang Tan, "An Average-Case Depth Hierarchy Theorem for Boolean Circuits", *56th IEEE Symposium on Foundations of Computer Science (FOCS 2015)*, 2015, https://doi.org/10.1109/FOCS.2015.67; numbering as in arXiv:1504.03398v1 (Section 1, main theorem; Section 1.2, first and second main lower bounds; Section 5.4, Definition of projection; Section 6, the balanced Sipser function; Section 9.1, projection switching lemma).
