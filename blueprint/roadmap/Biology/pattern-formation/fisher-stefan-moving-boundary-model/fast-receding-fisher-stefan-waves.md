# Fast receding Fisher–Stefan waves

**Setting.** Consider receding [Fisher–Stefan travelling waves](fisher-stefan-travelling-waves.md) with speed $c \to -\infty$: $U'' + cU' + U(1-U) = 0$ on $z < 0$, $U(-\infty) = 1$, $U(0) = 0$, $\kappa = -c/U'(0)$.

**Proposition (boundary layer).** Dividing by $c^2$ makes the problem singular as $1/c \to 0$. The outer solution is $U \equiv 1$. In the inner variable $\zeta = cz \in (0, \infty)$ the equation becomes

$$\frac{d^2U}{d\zeta^2} + \frac{dU}{d\zeta} + \frac{1}{c^2}U(1-U) = 0,$$

and the expansion $U = U_0 + c^{-2}U_1 + c^{-4}U_2 + O(c^{-6})$ with $U_k(0) = 0$, $U_0 \to 1$, $U_{k\ge1} \to 0$ as $\zeta \to \infty$ has

$$U_0(\zeta) = 1 - e^{-\zeta},\qquad U_1(\zeta) = \Big(\zeta - \frac12\Big)e^{-\zeta} + \frac12 e^{-2\zeta}.$$

Consequently

$$\kappa(c) = -1 + \frac{1}{2c^2} + O(c^{-4})\qquad(c \to -\infty),$$

so $\kappa \to -1^{+}$, and inversely

$$c \sim -\frac{1}{\sqrt{2(\kappa+1)}}\qquad(\kappa \to -1^{+}).$$

Receding waves therefore require $-1 < \kappa < 0$, and the front becomes a boundary layer of width $O(1/|c|)$ at the moving edge.

This corrects the source as printed in two places. Equations (31)–(35) of arXiv:2008.00662v3 pose the inner problem on "$-\infty < \zeta < 0$", with far conditions "$U_0 \to 1$ as $\zeta \to -\infty$" and $U_1, U_2 \to 0$ as $\zeta \to -\infty$; but $\zeta = zc$ with $z < 0$ and $c < 0$ gives $\zeta > 0$, the limit $z \to -\infty$ is $\zeta \to +\infty$, and the source's own solution (36), $U_0 = 1 - e^{-\zeta}$, tends to $1$ only as $\zeta \to +\infty$. Sections 1 and 4 print "$c \sim 2^{-1}(\kappa + 1)^{-1/2}$ as $\kappa \to -1^+$"; but the source's (43), $\kappa = -1 + \frac{1}{2c^2} + O(c^{-4})$, gives $c^2 \sim \frac{1}{2(\kappa+1)}$, that is $|c| \sim 2^{-1/2}(\kappa+1)^{-1/2}$, and $c < 0$ for receding waves fixes the sign.

## Depends on

- [Invading and receding Fisher–Stefan travelling waves](fisher-stefan-travelling-waves.md)

## Proof depends on

- [Invading and receding Fisher–Stefan travelling waves](fisher-stefan-travelling-waves.md)

## Expansion

With $z = \zeta/c$, $U_z = cU_\zeta$ and $U_{zz} = c^2U_{\zeta\zeta}$, giving the inner equation. At leading order $U_0'' + U_0' = 0$ with the boundary conditions gives $U_0 = 1 - e^{-\zeta}$, which matches the outer solution. The next order solves $U_1'' + U_1' = -U_0(1-U_0) = -e^{-\zeta} + e^{-2\zeta}$, and the displayed $U_1$ satisfies it with $U_1(0) = 0$. Then $U'(0) = c\,(U_0'(0) + c^{-2}U_1'(0) + \dots) = c\,(1 + \tfrac{1}{2c^2} + \dots)$, so $\kappa = -c/U'(0) = -1 + \tfrac{1}{2c^2} + O(c^{-4})$. Solving $\kappa + 1 \approx 1/(2c^2)$ with $c < 0$ gives the inverse relation; the paper also gives the $O(c^{-4})$ term, which is accurate already for $c < -2$.

## Sources

- M. El-Hachem, S. W. McCue and M. J. Simpson, "Invading and receding sharp-fronted travelling waves", Bulletin of Mathematical Biology (2021), <https://doi.org/10.1007/s11538-021-00862-y>. Numbering as in the preprint arXiv:2008.00662v3 (<https://arxiv.org/abs/2008.00662>): Section 3.3.3, Equations (29)–(44).
