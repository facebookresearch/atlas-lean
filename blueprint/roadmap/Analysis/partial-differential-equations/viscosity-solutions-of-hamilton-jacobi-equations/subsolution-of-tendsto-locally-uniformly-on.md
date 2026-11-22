# Stability of viscosity subsolutions under locally uniform limits

Let $F$ be jointly continuous and $\Omega$ open in a finite-dimensional real inner product space.
If $u_n$ are continuous viscosity subsolutions of $F(x, u, Du) = 0$ on $\Omega$ and $u_n \to U$ locally
uniformly on $\Omega$, then $U$ is a viscosity subsolution on $\Omega$.

Given a $C^1$ function $\varphi$ with $U - \varphi$ maximal at $x_0$, replace $\varphi$ by
$\psi = \varphi + |x - x_0|^2$, which makes the maximum strict without changing $D\varphi(x_0)$.
Maximisers $x_n$ of $u_n - \psi$ on a small closed ball converge to $x_0$, hence are interior for
large $n$, so $F(x_n, u_n(x_n), D\psi(x_n)) \le 0$; continuity of $F$ and of $D\psi$ passes this
to the limit. This is the locally uniform case of Lemma 6.1 of the user's guide, which treats merely
upper semicontinuous $u_n$ through the half-relaxed limit $\limsup^*$ and allows the equation to
vary with $n$ (Remark 6.3); neither generality is claimed here.

## Sources

- M. G. Crandall, H. Ishii and P.-L. Lions, "User's guide to viscosity solutions of second order partial differential equations", Bull. Amer. Math. Soc. 27 (1992), 1–67, arXiv:math/9207212, Lemma 6.1 and Remark 6.4.
