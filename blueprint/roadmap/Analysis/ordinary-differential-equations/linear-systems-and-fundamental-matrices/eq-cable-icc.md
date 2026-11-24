# Inlet data determine voltage and current on a finite cable

Let $r_m,r_i>0$ and $L\in\mathbb R$. Suppose that at every point of $[0,L]$ the real functions $V$ and $I$ have derivatives within that interval given by $V'=-r_i I$ and $I'=-V/r_m$. Write $\lambda=\sqrt{r_m/r_i}$ and $Z=\sqrt{r_m r_i}$. Then at every $x\in[0,L]$ both values are determined by the inlet data:

$$V(x)=V(0)\cosh(x/\lambda)-ZI(0)\sinh(x/\lambda),\qquad I(x)=I(0)\cosh(x/\lambda)-\frac{V(0)}{Z}\sinh(x/\lambda).$$

Thus any two steady states with the same inlet voltage and current agree throughout the interval.
