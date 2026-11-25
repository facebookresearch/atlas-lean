# Forced leapfrog stability bound

Let $h > 0$, $c > 0$, $\Delta t > 0$, and $c\,\Delta t/h \le \rho < 1$. Let $S$ be the periodic leapfrog step $S(u, v) = (u + c\,\Delta t\, D_+ v', v')$ with $v' = v - c\,\Delta t\, D_+^{*} u$, where $D_+$ is the periodic forward difference and $D_+^{*}$ its transpose, and let $\lVert (a,b) \rVert = \sqrt{h\sum_j a_j^2 + h\sum_j b_j^2}$. If pairs $E_k$, $F_k$ satisfy $E_{k+1} = S(E_k) + F_k$ and $\lVert F_k \rVert \le \varphi$ for all $k$, then for every $n$

$$\lVert E_n \rVert \le \sqrt{\frac{1+\rho}{1-\rho}}\left(\lVert E_0 \rVert + n\,\varphi\right).$$
