# Composed energy-norm error bound

For the same two-cell bar under the quadratic load $Q(x/L)^2$, let $\beta = QL^2/EA$ and $u(x) = \beta\hat u_2(x/L)$ with $\hat u_2(\xi) = (\xi - \xi^4)/12$; the exact interior load is $F = \int_0^LQ(x/L)^2\varphi(x/L)\,dx$, the composite midpoint load is $F_{mid} = \tfrac L2\bigl(Q(\tfrac14)^2\varphi(\tfrac14) + Q(\tfrac34)^2\varphi(\tfrac34)\bigr)$, and the coefficients are $c = F/K$ and $c_{mid} = F_{mid}/K$ with $K = 4EA/L$. For an approximate coefficient $\tilde c$, the midpoint residual is $r = F_{mid} - K\tilde c$, and $\tilde u_h(x) = \tilde c\,\varphi(x/L)$. If $EA > 0$ and $L > 0$, then

$$\Bigl(\int_0^LEA\bigl((u - \tilde u_h)'\bigr)^2\Bigr)^{1/2} \le \Bigl(\int_0^LEA\bigl((u - c\,\varphi(x/L))'\bigr)^2\Bigr)^{1/2} + \sqrt K\,\frac{|\beta|}{384} + \sqrt K\,\frac{L|r|}{4EA}.$$
