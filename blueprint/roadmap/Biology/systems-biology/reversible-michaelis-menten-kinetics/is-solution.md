# Solution of the reversible Michaelis–Menten system

For real rate constants $k_1, k_{-1}, k_2, k_{-2}$, functions
$s, c, e, p : \mathbb{R} \to \mathbb{R}$ (substrate, complex, free enzyme, product) solve the
reversible Michaelis–Menten system on $[0, \infty)$ when, at every $t \ge 0$, they have two-sided
derivatives with

$$
\begin{aligned}
s' &= -k_1 e s + k_{-1} c, & c' &= k_1 e s - (k_{-1} + k_2)\, c + k_{-2}\, e p,\\
e' &= -c', & p' &= k_2 c - k_{-2}\, e p.
\end{aligned}
$$

Here $k_1$ is the binding, $k_{-1}$ the unbinding of $S$, $k_2$ the catalysis and $k_{-2}$ the
rebinding of $P$ in the mechanism $E + S \rightleftharpoons C \rightleftharpoons E + P$.
