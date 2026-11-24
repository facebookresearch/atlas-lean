# Closed range passes to the adjoint

Let $E$ and $F$ be Hilbert spaces over $\mathbb{K}$,
where $\mathbb{K}$ is $\mathbb{R}$ or $\mathbb{C}$, and let $T : E \to F$ be a bounded linear
operator with adjoint $T^\dagger$. If the range of $T$ is closed in $F$, then the range of
$T^\dagger$ is closed in $E$.

Proof sketch: if the range of $T$ is closed, then $T$ is bounded below on $(\ker T)^\perp$
(the anti-Lipschitz criterion for its injective restriction), say $\|x\| \le C \|T x\|$ there.
Every $y \in (\ker T^\dagger)^\perp$ lies in the range of $T$, because
$(\operatorname{ran} T)^\perp = \ker T^\dagger$ and the range is closed. Writing $y = T x$ with
$x \in (\ker T)^\perp$ gives
$\|y\|^2 = \operatorname{Re} \langle x, T^\dagger y \rangle \le \|x\| \|T^\dagger y\| \le
C \|y\| \|T^\dagger y\|$; cancelling $\|y\|$ shows that $T^\dagger$ is bounded below on
$(\ker T^\dagger)^\perp$, so its range, which is the range of its restriction to
$(\ker T^\dagger)^\perp$, is closed.
