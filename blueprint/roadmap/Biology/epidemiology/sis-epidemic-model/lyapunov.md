# Goh–Volterra Lyapunov function of the SIS endemic equilibrium

For real numbers $\beta$, $\gamma$, $N$, $S$ and $I$, let $S^* = N\gamma/\beta$ and
$I^* = N(1 - \gamma/\beta)$ (for $0 < \gamma < \beta$ and $N > 0$, the endemic equilibrium of the
SIS model), and

$$V(S, I) = \left(S - S^* - S^* \log(S/S^*)\right) + \left(I - I^* - I^* \log(I/I^*)\right).$$

The intended domain is $0 < \gamma < \beta$ (that is, $\gamma > 0$ and $R_0 = \beta/\gamma > 1$),
$N > 0$ and $S, I > 0$: there $S^*, I^* > 0$, both logarithms are of positive numbers, and $V$
serves as a Lyapunov function for the endemic equilibrium. For other real inputs the formula is
evaluated with the conventions $x/0 = 0$, $\log 0 = 0$ and $\log x = \log|x|$ for $x < 0$; for
example, for $\beta = 0$ it gives $S^* = 0$ and $I^* = N$, so $V(S, I) = S + (I - N - N\log(I/N))$.
