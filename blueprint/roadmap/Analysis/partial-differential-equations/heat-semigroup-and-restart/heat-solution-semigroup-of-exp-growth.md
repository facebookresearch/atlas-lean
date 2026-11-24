# Heat Solution semigroup of exp growth

Let $P_hg$ denote the whole-line Gaussian heat evolution, with the stationary
extension $P_hg=g$ for $h\le0$. Write
\[
D_\nu f(t,x)=\int_0^tP_{\nu(t-s)}(f(s,\cdot))(x)\,ds.
\]

Let $g:\mathbb R\to\mathbb R$ be continuous with $|g(x)|\le M e^{c|x|}$ for some
$M,c\ge0$ and all $x$. If $s,t\ge0$, then, for every $x\in\mathbb R$,
\[
P_t(P_sg)(x)=P_{s+t}g(x).
\]
Both zero-time endpoints are included. No initial derivative, boundedness of $g$,
or negative-time semigroup law is assumed or asserted. The proof applies heat
uniqueness to the shifted solution.

The proof uses the exponential-growth special case of whole-line heat uniqueness from
[Stanford Math 220B, *Heat Equation*, Theorem 20](https://web.stanford.edu/class/math220b/handouts/heateqn.pdf).
The source permits quadratic-exponential growth, a larger class than needed here.
