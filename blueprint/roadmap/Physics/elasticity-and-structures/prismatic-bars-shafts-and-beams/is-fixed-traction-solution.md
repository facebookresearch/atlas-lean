# Bar fixed at one end and loaded by an end force

Let $k$, $L$ and $P$ be real numbers and $f, u \colon \mathbb{R} \to \mathbb{R}$. The function $u$
solves the fixed-traction problem on $[0, L]$ with rigidity $k$, distributed load $f$ and end force
$P$ if $u$ is twice continuously differentiable on $[0, L]$ and

$$-k\, u''(x) = f(x) \quad (x \in [0, L]), \qquad u(0) = 0, \qquad k\, u'(L) = P,$$

with the derivatives taken within $[0, L]$ (one-sided at the ends).

It models a bar of axial rigidity $k = EA$, fixed at $x = 0$ and loaded at $x = L$ by the end force
$P$, positive along the outward normal $+x$ (tension positive), under the distributed axial load
$f$, positive along $+x$; $k\, u'$ is the internal axial force. A circular shaft fixed at $x = 0$,
with $k = GJ$, distributed torque $f$ and end torque $P$, is the same problem
([shaft reading](twist.md)). The model has $L > 0$ and $k > 0$; the definition allows any real $k$,
$L$ and $P$. For $L \le 0$ the derivative within $[0, L]$ at $L$ is $0$ by convention, so the end
condition reads $P = 0$.
