# Cross-world counterfactuals are not identified by interventional laws

There are two binary structural causal models $M_1, M_2$ on $X \to Y$ with noise in $\{0,1\}^2$ such that

- the noise weights of both are probability mass functions;
- for every intervention $i$ on the observed nodes (including the observational regime) and all $x, y \in \{0,1\}$, the two models give the event $X = x,\ Y = y$ the same probability under $i$;
- yet they assign different probabilities to the cross-world event $Y_1 = 1,\ Y_0 = 0$, where the potential outcomes $Y_1 = f_Y(1, u)$ and $Y_0 = f_Y(0, u)$ share the noise $u$.
