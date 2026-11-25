# Residuals as componentwise perturbations

Let $K$ be a linearly ordered field, $M$ an $n \times n$ matrix over $K$, $x, r \in K^n$ and $g \ge 0$ in $K$. If

$$|r_i| \le g \sum_k |M_{ik}|\,|x_k| \quad \text{for every } i,$$

then there is an $n \times n$ matrix $\delta M$ with $|\delta M_{ik}| \le g\,|M_{ik}|$ for all $i, k$ and $\delta M\, x = r$.

One can take $\delta M_{ik} = r_i\,|M_{ik}|\,|x_k| / (S_i\, x_k)$ with $S_i = \sum_k |M_{ik}|\,|x_k|$, and $\delta M_{ik} = 0$ when $S_i = 0$ or $x_k = 0$. This is the construction behind the Oettli–Prager characterisation of componentwise backward error (here with only the matrix perturbed), and it is how a residual bound becomes a backward error.
