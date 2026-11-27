# Voltage profile and inlet relation for a cable with a sealed end

Let $r_m,r_i,L>0$, $\lambda=\sqrt{r_m/r_i}$ and $Z=\sqrt{r_m r_i}$. Suppose the voltage $V$ and axial current $I$ satisfy $V'=-r_i I$ and $I'=-V/r_m$ on $[0,L]$, with derivatives taken within the interval. If the far end is sealed, meaning $I(L)=0$, then the inlet voltage and current satisfy

$$V(0)\sinh(L/\lambda)=ZI(0)\cosh(L/\lambda).$$

The voltage at every $x\in[0,L]$ is

$$V(x)=V(0)\,\frac{\cosh((L-x)/\lambda)}{\cosh(L/\lambda)}.$$
