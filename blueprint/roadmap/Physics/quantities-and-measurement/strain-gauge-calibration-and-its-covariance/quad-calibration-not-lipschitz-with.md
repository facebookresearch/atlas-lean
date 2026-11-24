# For nonzero c2 the quadratic calibration is not Lipschitz on the line

For real $c_0$, $c_1$ and $c_2 \ne 0$, the [quadratic calibration](quad-calibration.md)
$f(v) = c_0 + c_1 v + c_2 v^2$ is not Lipschitz on $\mathbb{R}$ with any constant $K \ge 0$: for no
$K \ge 0$ does $|f(v) - f(w)| \le K\,|v - w|$ hold for all real $v$ and $w$. So a global Lipschitz
error budget, which bounds the output error by a constant times the input error, does not apply to
it. For $c_2 = 0$ the calibration is affine, and Lipschitz with constant $|c_1|$.
