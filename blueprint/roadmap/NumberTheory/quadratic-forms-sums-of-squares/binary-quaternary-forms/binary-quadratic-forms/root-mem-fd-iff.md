# Roots in Mathlib's closed fundamental domain

Let $a, b, c \in \mathbb{Z}$ with $a > 0$,
and let $\tau$ be a root of $a\tau^2 + b\tau + c = 0$ in the upper half-plane.
Then $\tau$ lies in the closed fundamental domain `ModularGroup.fd`,
$\{\tau \in \mathbb{H} : |\tau|^2 \ge 1,\ |\mathrm{re}(\tau)| \le 1/2\}$, if and only if
$|b| \le a \le c$.

The computation $\mathrm{re}(\tau) = -b/(2a)$, $|\tau|^2 = c/a$ is written out here; compare the
half-open domain $F$ of Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT
OpenCourseWare, Fall 2025, Lecture 15, before Lemma 15.10.
