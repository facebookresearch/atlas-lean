# Aldous's tightness criterion in D([0,1])

Let $\mu$ be a probability measure and $(\xi_{n,i})$ a triangular array of real random variables with row $n$ adapted to a filtration $\mathcal F_n$ ($\xi_{n,i}$ is $\mathcal F_{n,i+1}$-measurable). Let $S_{n,k} = \sum_{i<k} \xi_{n,i}$. Suppose:

- for every $\varepsilon > 0$, $\mu(\exists i < n,\ |\xi_{n,i}| > \varepsilon) \to 0$;
- Aldous's condition: for all $\varepsilon, \eta > 0$ there are $\theta > 0$ and $N$ such that for all $n \ge N$ and all $\mathcal F_n$-stopping times $\sigma \le \rho \le \sigma + \lfloor n\theta \rfloor$ with $\rho \le n$, $\mu(|S_{n,\rho} - S_{n,\sigma}| \ge \varepsilon) \le \eta$.

Then the laws of the step processes $t \mapsto S_{n,\lfloor n t\rfloor}$ in $D([0,1])$ are tight for the Skorokhod $J_1$ topology.

## Sources

- J. Jacod and A. N. Shiryaev, *Limit Theorems for Stochastic Processes*, 2nd ed., Springer (2003), Theorem VI.4.5 and Proposition VI.3.26.
- D. Aldous, Stopping times and tightness, *Ann. Probab.* 6 (1978), 335-340.
