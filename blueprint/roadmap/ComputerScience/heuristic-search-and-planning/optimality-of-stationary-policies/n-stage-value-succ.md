# Appending a stage at the end

For every Markov policy $\pi = (\mu_0, \mu_1, \dots)$, every $N$ and every terminal value $V$, the $(N+1)$-stage value of $\pi$ with terminal value $V$ equals its $N$-stage value with terminal value $T_{\mu_N} V$:

$$T_{\mu_0} \cdots T_{\mu_{N-1}} T_{\mu_N} V = T_{\mu_0} \cdots T_{\mu_{N-1}} \big(T_{\mu_N} V\big).$$

The definition peels off the first stage; this identity peels off the last.
