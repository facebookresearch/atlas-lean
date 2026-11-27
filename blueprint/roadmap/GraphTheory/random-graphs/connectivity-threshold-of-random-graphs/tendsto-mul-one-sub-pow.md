# First moment of isolated vertices at the connectivity threshold

If $p_n$ are real numbers with $n p_n - \log n \to c$ (for example $p_n = (\log n + c)/n$ for $n \ge 1$), then $n(1 - p_n)^{n-1}$, which for $0 \le p_n \le 1$ is the expected number of isolated vertices of $G(n, p_n)$, satisfies

$$n(1 - p_n)^{n-1} \to e^{-c}.$$

Proof: write $c_n = n p_n - \log n$ and $n(1-p_n)^{n-1} = \exp\big(\log n + (n-1)\log(1 - p_n)\big)$. The bounds $-x/(1-x) \le \log(1-x) \le -x$ squeeze the exponent between $-c_n + p_n - (n-1)p_n^2/(1-p_n)$ and $-c_n + p_n$. Both tend to $-c$, since $p_n \to 0$ and $n p_n^2 = (\log n + c_n)^2/n \to 0$.

The source states this limit, (3.1), under the same hypothesis $np - \log n \to c$, together with the cases $np - \log n \to \pm\infty$ (limits $0$ and $\infty$).

## Sources

- A. Frieze and M. Karoński, *Introduction to Random Graphs*, Cambridge University Press (2016), Section 3.1, equation (3.1) and the computation (3.3) in the proof of Theorem 3.1.
