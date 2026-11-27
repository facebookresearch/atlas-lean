# Comp

Request-preserving simulations compose. Let the first simulation reduce $X$ to $Y$ with coefficients $(a_1, p_1, d_1, q_1)$ and the second reduce $Y$ to $Z$ with coefficients $(a_2, p_2, d_2, q_2)$; here a simulation of $X$ by $Y$ turns every strategy for $Y$ into one for $X$ with cost at most $a \cdot \mathrm{cost}_Y + p$ on legal inputs, and turns every feasible trace of $X$ into one of $Y$ on the same requests with cost at most $d \cdot \mathrm{cost}_X + q$. Then the composite simulates $X$ by $Z$ with coefficients
$$(a_1 a_2,\ a_1 p_2 + p_1,\ d_1 d_2,\ d_2 q_1 + q_2).$$
