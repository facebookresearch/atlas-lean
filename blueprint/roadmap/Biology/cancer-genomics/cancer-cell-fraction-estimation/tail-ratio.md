# Posterior tail probability on a grid

For a finite index set $I$, real prior weights $\pi_i$, likelihoods $L_i$ and parameter values $c_i$ ($i \in I$), and a real threshold $t$, the posterior tail is

$$\mathrm{Tail}(\pi, L, c; t) = \frac{\sum_{i \,:\, c_i > t} \pi_i L_i}{\sum_{i} \pi_i L_i},$$

with the convention $x/0 = 0$. It is a posterior probability when the weights $\pi_i L_i$ are nonnegative with positive total.
