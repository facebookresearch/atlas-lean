# Bounded recovery from modular spectral averages

Use a complete complex Hilbert space $H$, a represented von Neumann algebra $M$, a cyclic separating unit vector $\xi$, a conjugate-linear isometric involution $J$, and a unital star calculus $D:C_b(\mathbb R)\to\mathcal B(H)$. Require that the vectors $D(f)k$ for compactly supported $f$ form a dense set. Put $U_t=D(e^{itu})$. Require that the closure of the graph $(a\xi,a^*\xi)$ for $a\in M$ consists exactly of $(h,Jq)$ with $D(e^{\min(n,u)/2})h\to q$ as $n\to\infty$. Also require the scalar centralizer condition: elements of $M$ fixed by every $a\mapsto U_t aU_{-t}$ are scalar.

Fix a free ultrafilter $\omega$ on $\mathbb N$, a bounded complex-linear $T$, a real $s$, positive $\delta_n\to0$ and unit vectors $h_n$ supported in $[s-\delta_n,s+\delta_n]$ for $D$. Here support in $I$ means $D(f)h=0$ for every bounded continuous $f$ vanishing on $I$. Suppose the upper limit over $n$ of the $\omega$-limit over integer $k$ of $(2k)^{-1}\int_{-k}^k\|TU_t h_n\|^2dt$ is positive. Then there exist a strictly increasing subsequence $n_j$, operators $v_j\in M$ and real $C,\eta$ with $\eta>0$, such that $\|v_j\|\leq C$, $\|Tv_j\xi\|\geq\eta$, and $v_j\xi$ is supported in $[s-4\delta_{n_j},s+4\delta_{n_j}]$ for every $j$. At $k=0$ the average has the source's harmless totalized value.

## Depends on
The nondegenerate bounded functional calculus and exact closed graph, fixed ultrafilter, and spectral support stated by annihilation.

## Proof depends on
The bounded algebra-element recovery step and a modular spectral cutoff that preserves the required norm lower bound while enlarging bands by at most four.

## Expansion
Verify the calculus and graph bridge to ordinary modular data. Isolate selection from the positive limsup, uniform bound on the recovered elements, and the final spectral support computation. Do not replace this by a bicentralizer-triviality statement.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BoundedRecovery.lean#L88-L97) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/290.md).
