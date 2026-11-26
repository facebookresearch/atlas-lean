# Probability of the cross-world event Y₁ = 1, Y₀ = 0

For a binary structural causal model on $X \to Y$ with noise in a finite type $U$, weights $p_U$ and structural equation $Y = f_Y(X, u)$, the potential outcomes are $Y_1(u) = f_Y(1, u)$ and $Y_0(u) = f_Y(0, u)$, evaluated at the same noise $u$. The weight of the cross-world event is

$$P(Y_1 = 1, Y_0 = 0) = \sum_{u \in U :\ f_Y(1,u) = 1,\ f_Y(0,u) = 0} p_U(u),$$

a probability when the weights form a probability mass function.
