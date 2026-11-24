# Heat Duhamel restart

Let $P_hg$ denote whole-line Gaussian heat evolution, with the stationary
extension $P_hg=g$ for $h\le0$, and put
\[
D_\nu f(t,x)=\int_0^t P_{\nu(t-s)}(f(s,\cdot))(x)\,ds.
\]
Assume $f:[0,T]\times\mathbb R\to\mathbb R$ is jointly continuous and, for some
$M,c\ge0$, satisfies $|f(s,x)|\le M e^{c|x|}$ for all $s\in[0,T]$ and $x\in\mathbb R$.
No continuity outside the strip or spatial/time differentiability is required.


For $\nu\ge0$, $a,b\ge0$, $a+b\le T$ and every $x\in\mathbb R$,
\[
D_\nu f(a+b,x)=P_{\nu b}(D_\nu f(a,\cdot))(x)
+D_\nu\bigl((s,y)\mapsto f(a+s,y)\bigr)(b,x).
\]
This includes zero viscosity and zero elapsed times. The second term uses the shifted
forcing; no classical PDE or initial-time derivative is assumed.

The proof uses whole-line heat uniqueness from
[Stanford Math 220B, *Heat Equation*, Theorem 20](https://web.stanford.edu/class/math220b/handouts/heateqn.pdf)
and Gaussian domination for finite-time integral interchange.
