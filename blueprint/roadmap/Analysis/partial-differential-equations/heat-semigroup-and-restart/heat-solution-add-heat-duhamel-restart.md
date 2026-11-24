# Heat Solution add heat Duhamel restart

Let $P_hg$ denote whole-line Gaussian heat evolution, with the stationary
extension $P_hg=g$ for $h\le0$, and put
\[
D_\nu f(t,x)=\int_0^t P_{\nu(t-s)}(f(s,\cdot))(x)\,ds.
\]
Assume $f:[0,T]\times\mathbb R\to\mathbb R$ is jointly continuous and, for some
$M,c\ge0$, satisfies $|f(s,x)|\le M e^{c|x|}$ for all $s\in[0,T]$ and $x\in\mathbb R$.
No continuity outside the strip or spatial/time differentiability is required.


Let $g:\mathbb R\to\mathbb R$ also be continuous and of exponential growth, with
its own nonnegative constants. For $\nu\ge0$, $a,b\ge0$, $a+b\le T$ and every $x$,
\[
P_{\nu(a+b)}g(x)+D_\nu f(a+b,x)
=P_{\nu b}\bigl(P_{\nu a}g+D_\nu f(a,\cdot)\bigr)(x)
+D_\nu\bigl((s,y)\mapsto f(a+s,y)\bigr)(b,x).
\]
The full initial-data-plus-forcing construction therefore restarts from its accumulated
value. Continuity and growth of both accumulated terms are proved before using
linearity. No initial derivative is required.

The proof uses whole-line heat uniqueness from
[Stanford Math 220B, *Heat Equation*, Theorem 20](https://web.stanford.edu/class/math220b/handouts/heateqn.pdf)
and Gaussian domination for finite-time integral interchange.
