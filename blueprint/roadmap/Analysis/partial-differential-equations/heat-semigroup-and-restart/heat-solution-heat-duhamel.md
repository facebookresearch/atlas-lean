# Heat Solution heat Duhamel

Let $P_hg$ denote whole-line Gaussian heat evolution, with the stationary
extension $P_hg=g$ for $h\le0$, and put
\[
D_\nu f(t,x)=\int_0^t P_{\nu(t-s)}(f(s,\cdot))(x)\,ds.
\]
Assume $f:[0,T]\times\mathbb R\to\mathbb R$ is jointly continuous and, for some
$M,c\ge0$, satisfies $|f(s,x)|\le M e^{c|x|}$ for all $s\in[0,T]$ and $x\in\mathbb R$.
No continuity outside the strip or spatial/time differentiability is required.


For $\nu\ge0$, $t\in[0,T]$, $h\ge0$ and every $x\in\mathbb R$,
\[
P_h(D_\nu f(t,\cdot))(x)=\int_0^tP_{\nu(t-s)+h}(f(s,\cdot))(x)\,ds.
\]
The hypotheses discharge all integrability requirements. The proof combines
finite-time integral interchange with the nonnegative-time semigroup law.

The proof uses whole-line heat uniqueness from
[Stanford Math 220B, *Heat Equation*, Theorem 20](https://web.stanford.edu/class/math220b/handouts/heateqn.pdf)
and Gaussian domination for finite-time integral interchange.
