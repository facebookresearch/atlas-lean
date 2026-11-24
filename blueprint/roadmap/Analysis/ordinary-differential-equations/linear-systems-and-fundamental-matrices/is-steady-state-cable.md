# Transfer solution for a uniform cable

Let $r_m,r_i>0$, and set $\lambda=\sqrt{r_m/r_i}$ and $Z=\sqrt{r_m r_i}$. For any real inlet values $V_0,I_0$, define the voltage and current by

$$V(x)=V_0\cosh(x/\lambda)-ZI_0\sinh(x/\lambda),\qquad I(x)=I_0\cosh(x/\lambda)-(V_0/Z)\sinh(x/\lambda).$$

On any set $S\subseteq\mathbb R$, these functions solve the steady cable equations: at every $x\in S$, $V$ has derivative $-r_i I(x)$ within $S$, and $I$ has derivative $-V(x)/r_m$ within $S$. The formulas give $V(0)=V_0$ and $I(0)=I_0$ whether or not $0\in S$.
