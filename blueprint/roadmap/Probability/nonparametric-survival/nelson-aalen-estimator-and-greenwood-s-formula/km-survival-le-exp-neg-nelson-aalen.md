# Kaplan–Meier is below the exponentiated Nelson–Aalen estimate

For grouped right-censored data, $\hat S(t) \le \exp(-\hat A(t))$ for every real $t$, since each factor
satisfies $1 - d_j / Y_j \le \exp(-d_j / Y_j)$. Here a ratio $d_j / Y_j$ is $0$ when nobody is at risk
($Y_j = 0$, hence $d_j = 0$), so that time's factor is $1$ and its Nelson–Aalen increment $0$.
