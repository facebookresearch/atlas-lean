# No supersaturation inside layers under the Clausius-Clapeyron curve

Let $e_{s0}, L, R_v, T_0 > 0$ and let $p_{\mathrm{sat}}(T) = e_{s0} \exp\!\left(\frac{L}{R_v}\left(\frac{1}{T_0} - \frac{1}{T}\right)\right)$. Take face temperatures $T_0', \dots, T_n'$ with $T_i' > 0$ for all $i \le n$ and face vapor pressures $P_i$ such that for every layer $i < n$,

$$\max(P_i, P_{i+1}) \le p_{\mathrm{sat}}(\min(T_i', T_{i+1}')).$$

Then for every layer $i < n$ and every $\theta \in [0,1]$, with linear interpolants $T(\theta) = (1-\theta) T_i' + \theta T_{i+1}'$ and $P(\theta) = (1-\theta) P_i + \theta P_{i+1}$, we have $T(\theta) > 0$ and $P(\theta) \le p_{\mathrm{sat}}(T(\theta))$.
