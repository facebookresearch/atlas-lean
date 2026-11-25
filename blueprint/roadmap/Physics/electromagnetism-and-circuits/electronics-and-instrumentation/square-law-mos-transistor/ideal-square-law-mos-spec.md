# Properties of the ideal square-law MOS model for $\beta > 0$

Let $\beta > 0$ and write $I(u, V_{DS})$ for the [square-law drain current](current.md),
$I_{\mathrm{tri}}$ for the [triode formula](triode-current.md) and $I_{\mathrm{sat}}$ for the
[saturation formula](saturation-current.md). Then all of the following hold, for all real $u$,
$V_{DS}$ satisfying the stated conditions:

1. $I(u, V_{DS}) = 0$ if $V_{DS} \ge 0$ and $u \le 0$;
2. $I(u, V_{DS}) = I_{\mathrm{tri}}(u, V_{DS})$ if $V_{DS} \ge 0$, $u > 0$ and $V_{DS} \le u$;
3. $I(u, V_{DS}) = I_{\mathrm{sat}}(u)$ if $u > 0$ and $u \le V_{DS}$;
4. $I_{\mathrm{tri}}(u, u) = I_{\mathrm{sat}}(u)$ for every $u$;
5. for $V_{DS} \ge 0$, $I$ is continuous in $u$ at $u = 0$;
6. for $u > 0$, $I$ is continuous in $V_{DS}$ at $V_{DS} = u$;
7. for $u > 0$, $I$ is jointly continuous in $(u, V_{DS})$ at $(u, u)$;
8. for $u < 0$, $\partial I / \partial u = 0$ at $(u, V_{DS})$;
9. for $u < 0$, $\partial I / \partial V_{DS} = 0$ at $(u, V_{DS})$;
10. for $0 < V_{DS} < u$, $\partial I / \partial u = \beta V_{DS}$;
11. for $0 < V_{DS} < u$, $\partial I / \partial V_{DS} = \beta (u - V_{DS})$;
12. for $0 < u < V_{DS}$, $\partial I / \partial u = \beta u$;
13. for $0 < u < V_{DS}$, $\partial I / \partial V_{DS} = 0$;
14. $0 \le \beta (u - V_{DS})$ if $V_{DS} \le u$;
15. $I(u, V_{DS}) \ge 0$ if $V_{DS} \ge 0$.

The derivatives are the partial derivatives in the open regions only; no derivative on a region
boundary and no global smoothness is stated. In the physical reading $\beta > 0$ is the device
constant, $u = V_{GS} - V_{th}$ the gate overdrive and $V_{DS} \ge 0$ the drain–source voltage of a
forward-biased nMOS transistor.
