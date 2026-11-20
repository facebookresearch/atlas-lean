# Nelson–Aalen estimate of the cumulative hazard

For grouped right-censored data with $d_j$ deaths and $Y_j$ subjects at risk at the observation time
$t_j$, the Nelson–Aalen estimate of the cumulative hazard is
$$\hat A(t) = \sum_{t_j \le t} \frac{d_j}{Y_j}.$$
A time with nobody at risk ($Y_j = 0$, hence $d_j = 0$) contributes $0$: the ratio is taken to be $0$.
