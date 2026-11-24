# Heat Solution interval Integral of exp growth

Let $P_hg$ denote whole-line Gaussian heat evolution, with the stationary
extension $P_hg=g$ for $h\le0$, and put
\[
D_\nu f(t,x)=\int_0^t P_{\nu(t-s)}(f(s,\cdot))(x)\,ds.
\]
Assume $f:[0,T]\times\mathbb R\to\mathbb R$ is jointly continuous and, for some
$M,c\ge0$, satisfies $|f(s,x)|\le M e^{c|x|}$ for all $s\in[0,T]$ and $x\in\mathbb R$.
No continuity outside the strip or spatial/time differentiability is required.


For $t\in[0,T]$, arbitrary $h\in\mathbb R$ and $x\in\mathbb R$,
\[
P_h\left(\int_0^t f(s,\cdot)\,ds\right)(x)=\int_0^tP_h(f(s,\cdot))(x)\,ds.
\]
Gaussian exponential domination proves product integrability before applying Fubini.
Nonpositive $h$ uses the stationary extension; no backward heat equation is claimed.

The proof uses fixed-Gaussian rescaling, an integrable exponential majorant on the
product of the finite time interval with the spatial line, and Fubini's theorem.
It does not invoke heat uniqueness.
